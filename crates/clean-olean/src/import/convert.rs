// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constant conversion from parsed .olean format to kernel types.
//!
//! Converts `ParsedConstant` entries into `Declaration`, `InductiveVal`,
//! `ConstructorVal`, and `RecursorVal` kernel types for environment registration.

use super::convert_expr::{convert_expr, convert_level_params};
use super::export_fields::ExportFields;
use super::{ExprInternCache, ExprSharingStats, ImportError};
use crate::module::{ConstantKind, ParsedConstant, ReducibilityHintsData};
use clean_kernel::env::{ConstantKind as KernelConstantKind, Declaration, ProofValueElision};
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::inductive::{
    ConstructorVal, InductiveVal, RecursorArgOrder, RecursorRule, RecursorVal,
};
use clean_kernel::level::Level;
use clean_kernel::name::Name;

/// Map an olean constant kind to the kernel kind for the two PROOF kinds whose
/// VALUE the elision policy may drop; every other kind returns `None` (never
/// elided). Used to gate conversion-time proof-value elision on the SAME
/// predicate the post-hoc null uses, so the two produce an identical value=None set.
pub(super) fn olean_kind_to_kernel_proof(kind: &ConstantKind) -> Option<KernelConstantKind> {
    match kind {
        ConstantKind::Theorem => Some(KernelConstantKind::Theorem),
        ConstantKind::Opaque => Some(KernelConstantKind::Opaque),
        _ => None,
    }
}

/// True iff `elide` drops the proof VALUE for this olean kind. When true the
/// value DAG is never built/interned (removing the peak at the source rather than
/// nulling it post-hoc, which cannot reclaim the interned `Arc`s).
pub(super) fn elides_value(elide: ProofValueElision, kind: &ConstantKind) -> bool {
    olean_kind_to_kernel_proof(kind).is_some_and(|kk| elide.elides(kk))
}

/// Resolve the `Declaration` value for a proof kind (Theorem/Opaque): the
/// converted value when present; a trivial O(1) `Sort 0` PLACEHOLDER when it was
/// deliberately elided (the post-hoc null in `register_converted_constants` drops
/// it to `None` before it reaches the env, so it never enters the intern cache or
/// any verdict); otherwise a hard `MissingValue` error.
pub(super) fn proof_value_or_placeholder(
    value: Option<Expr>,
    elided: bool,
    name: &str,
) -> Result<Expr, ImportError> {
    match value {
        Some(v) => Ok(v),
        None if elided => Ok(Expr::sort(Level::zero())),
        None => Err(ImportError::MissingValue(name.to_owned())),
    }
}

/// True iff this olean kind is an INDUCTIVE FAMILY (Inductive/Constructor/Recursor)
/// that the kernel cannot serve lazily from a `.mathverse` shard (the shard format
/// carries no recursor rules / side tables). These are the only kinds converted +
/// registered eagerly under `ImportKinds::InductiveFamiliesOnly`; the definitional
/// kinds (Axiom/Definition/Theorem/Opaque/Quot — the `Other` bucket) are served by
/// the lazy `ShardConstantSource`, so their owned `Arc<Expr>` is never built.
///
/// SOUNDNESS: the converted SET is unchanged vs. the post-skip baseline —
/// `register_converted_constants` already early-returns for the `Other` bucket under
/// `InductiveFamiliesOnly`, so skipping their CONVERSION drops only wasted work, not
/// any registered constant. The 1:1 correspondence (this predicate ⇔ the non-`Other`
/// `ConvertedConstant` variants) is asserted by `test_inductive_family_kind_matches_variant`.
pub(super) fn is_inductive_family_kind(kind: &ConstantKind) -> bool {
    matches!(
        kind,
        ConstantKind::Inductive | ConstantKind::Constructor | ConstantKind::Recursor
    )
}

/// Converted constant with its original name for error reporting.
/// Each variant carries `ExprSharingStats` for the expressions it converted.
pub(crate) enum ConvertedConstant {
    Inductive(String, Result<InductiveVal, ImportError>, ExprSharingStats),
    Constructor(
        String,
        Result<ConstructorVal, ImportError>,
        ExprSharingStats,
    ),
    Recursor(
        String,
        Result<(RecursorVal, Vec<Name>, u32), ImportError>,
        ExprSharingStats,
    ),
    Other(
        String,
        Result<(Declaration, ExportFields), ImportError>,
        ExprSharingStats,
    ),
}

/// Convert Declaration to ConstantInfo, using parsed .olean hints when available.
///
/// When `hints` is `Some`, the reducibility is derived from the .olean binary data
/// (matching Lean 4's ReducibilityHints exactly). When `None`, falls back to the
/// `is_reducible` boolean.
#[inline]
/// Detect if an expression is a projection function body: `lam* . Proj(...)`.
///
/// In Lean 4, projection functions like `HPow.hPow` are always `Abbrev`
/// (reducible), but the .olean format stores them with `Regular(0)` hints
/// because the kernel uses `projFnExt` to recognize them. Since clean
/// doesn't parse `projFnExt`, we detect projection functions by their
/// value shape and override their reducibility to `Reducible`. Part of #3134.
pub fn is_projection_fn_body(expr: &Expr) -> bool {
    use clean_kernel::expr::ExprKind;
    let mut e = expr;
    loop {
        match e.kind() {
            ExprKind::Lam(_, _, body) => e = body,
            ExprKind::Proj(_, _, _) => return true,
            _ => return false,
        }
    }
}

/// True for Lean's parameter-annotation abbreviations, which `Init/Prelude.lean`
/// declares as `@[reducible] def … := α` reducible identities:
///
/// ```lean
/// @[reducible] def optParam      (α : Sort u) (default : α)        : Sort u := α
/// @[reducible] def autoParam     (α : Sort u) (syntax : Lean.Syntax) : Sort u := α
/// @[reducible] def outParam      (α : Sort u)                       : Sort u := α
/// @[reducible] def semiOutParam  (α : Sort u)                       : Sort u := α
/// ```
///
/// The `.olean` reducibility-hint payload for these does not always round-trip
/// as `Abbrev`; this list restores their source-true `Reducible` status so the
/// kernel unfolds a field/binder typed `autoParam X tac` to its bare `X` during
/// `is_def_eq` (the `*.instLinearOrder` `min_def`/`max_def` default-field check).
fn is_lean_reducible_identity_abbrev(name: &Name) -> bool {
    matches!(
        name.to_string().as_str(),
        "optParam" | "autoParam" | "outParam" | "semiOutParam"
    )
}

pub(crate) fn decl_to_constant_info(
    decl: Declaration,
    hints: Option<ReducibilityHintsData>,
) -> clean_kernel::env::ConstantInfo {
    match decl {
        Declaration::Definition {
            name,
            level_params,
            type_,
            value,
            is_reducible,
        } => {
            let mut reducibility = match hints {
                Some(ReducibilityHintsData::Opaque) => clean_kernel::env::Reducibility::Opaque,
                Some(ReducibilityHintsData::Abbrev) => clean_kernel::env::Reducibility::Reducible,
                Some(ReducibilityHintsData::Regular(h)) => {
                    clean_kernel::env::Reducibility::Regular(h)
                }
                None => {
                    // Fallback: use is_reducible boolean (for kernel-created declarations)
                    if is_reducible {
                        clean_kernel::env::Reducibility::Reducible
                    } else {
                        clean_kernel::env::Reducibility::Regular(0)
                    }
                }
            };
            // Projection functions must be Reducible for typeclass projection
            // chains to reduce (e.g., HPow.hPow → instHPow → Nat.pow).
            if !matches!(reducibility, clean_kernel::env::Reducibility::Reducible)
                && is_projection_fn_body(&value)
            {
                reducibility = clean_kernel::env::Reducibility::Reducible;
            }
            // Lean's parameter-annotation abbrevs are `@[reducible] def`
            // identities (`Init/Prelude.lean`): `optParam α default := α`,
            // `autoParam α syntax := α`, `outParam α := α`, `semiOutParam α := α`.
            // Some `.olean` reducibility-hint payloads surface them as plain
            // `Regular` rather than `Abbrev`; restore the source-true `Reducible`
            // status so a constructor field typed `autoParam X tac` (e.g. the
            // self-referential `min_def`/`max_def` defaults on `*.instLinearOrder`)
            // delta-reduces to its bare `X` during `is_def_eq`. SOUNDNESS: these
            // are genuine reducible identities upstream; making them `Reducible`
            // only changes the def-eq unfold tie-break (Reducibility never gates
            // `unfold_definition`, only `Opaque` does), never the reduction
            // relation — the kernel still fully proof-checks every value.
            if !matches!(reducibility, clean_kernel::env::Reducibility::Reducible)
                && is_lean_reducible_identity_abbrev(&name)
            {
                reducibility = clean_kernel::env::Reducibility::Reducible;
            }
            let is_reducible = matches!(reducibility, clean_kernel::env::Reducibility::Reducible);
            clean_kernel::env::ConstantInfo {
                name,
                level_params,
                type_,
                value: Some(value),
                reducibility,
                is_reducible,
                kind: clean_kernel::env::ConstantKind::Definition,
            }
        }
        Declaration::Axiom {
            name,
            level_params,
            type_,
        } => clean_kernel::env::ConstantInfo {
            name,
            level_params,
            type_,
            value: None,
            reducibility: clean_kernel::env::Reducibility::Regular(0),
            is_reducible: false,
            kind: clean_kernel::env::ConstantKind::Axiom,
        },
        Declaration::Theorem {
            name,
            level_params,
            type_,
            value,
        } => clean_kernel::env::ConstantInfo {
            name,
            level_params,
            type_,
            value: Some(value),
            reducibility: clean_kernel::env::Reducibility::Opaque,
            is_reducible: false,
            kind: clean_kernel::env::ConstantKind::Theorem,
        },
        Declaration::Opaque {
            name,
            level_params,
            type_,
            value,
        } => clean_kernel::env::ConstantInfo {
            name,
            level_params,
            type_,
            value: Some(value),
            reducibility: clean_kernel::env::Reducibility::Opaque,
            is_reducible: false,
            kind: clean_kernel::env::ConstantKind::Opaque,
        },
    }
}

/// Convert ONE non-inductive `ParsedConstant` (Definition / Theorem / Opaque /
/// Axiom / Quot) into a kernel [`Declaration`], using the SAME `convert_expr`
/// path the eager olean importer uses — so the resulting `Expr` is byte-identical
/// to the eager import. Returns `Ok(None)` for Inductive/Constructor/Recursor
/// kinds (those carry side tables a `Declaration` cannot, and the HYBRID lazy
/// closure loader serves them EAGERLY anyway).
///
/// Unlike `load_parsed_module`, this performs NO environment registration and
/// therefore NO dependency-resolution check, so a module's structure projections
/// and other decls whose types mention not-yet-loaded inductives still convert —
/// which is required when building a single module's `.mathverse` shard
/// standalone (the parity-faithful closure-shard builder).
pub fn convert_parsed_constant_to_declaration(
    constant: &ParsedConstant,
) -> Result<Option<Declaration>, ImportError> {
    match constant.kind {
        ConstantKind::Inductive | ConstantKind::Constructor | ConstantKind::Recursor => Ok(None),
        _ => {
            let mut intern = ExprInternCache::default();
            let (result, _stats) = convert_constant(constant, &mut intern, ProofValueElision::None);
            result.map(Some)
        }
    }
}

/// Like [`convert_parsed_constant_to_declaration`], but returns the full kernel
/// [`ConstantInfo`] — crucially carrying the constant's true `reducibility`
/// (derived from the olean `ReducibilityHintsData`: `@[reducible]`/Abbrev ->
/// `Reducible`, `Regular(height)`, `Opaque`), which a bare `Declaration`'s
/// `is_reducible` bool cannot represent.
///
/// The parity-faithful closure-shard builder needs this so the lazily-served
/// `ConstantInfo.reducibility` matches the eager olean import EXACTLY — the
/// kernel's δ-unfold ordering keys on it, so a `@[reducible]` def served as
/// `Regular(0)` reduces differently in is_def_eq and can flip a verdict.
/// Returns `Ok(None)` for inductive/constructor/recursor kinds (served eagerly).
pub fn convert_parsed_constant_to_const_info(
    constant: &ParsedConstant,
) -> Result<Option<clean_kernel::env::ConstantInfo>, ImportError> {
    ConstantConvertSession::default().const_info(constant)
}

/// A multi-constant conversion session sharing ONE expression intern cache
/// across every constant it converts — the #2383 cross-constant hash-consing
/// the module loader already enjoys, extended to callers that convert
/// constants one at a time (the per-constant demand walk previously minted a
/// FRESH cache per constant, so a 3–5k-constant closure shared zero subterms
/// and Mathlib's heavily repeated type/instance spines were duplicated per
/// constant — the dominant residual of the fix-#2 memory measurement).
///
/// VERDICT-NEUTRAL: interning returns an existing `Arc` only on FULL
/// structural equality, so every produced `ConstantInfo` is `Expr`-equal to
/// the fresh-cache result — verdicts and content digests are byte-identical;
/// only allocation/sharing differs. The session holds `Arc` clones that are
/// shared with the produced constants, so dropping the session frees only map
/// overhead, never expression data still in use.
#[derive(Default)]
pub struct ConstantConvertSession {
    intern: ExprInternCache,
}

impl ConstantConvertSession {
    /// Session-shared variant of [`convert_parsed_constant_to_const_info`].
    pub fn const_info(
        &mut self,
        constant: &ParsedConstant,
    ) -> Result<Option<clean_kernel::env::ConstantInfo>, ImportError> {
        match constant.kind {
            ConstantKind::Inductive | ConstantKind::Constructor | ConstantKind::Recursor => {
                Ok(None)
            }
            _ => {
                let (result, _stats) =
                    convert_constant(constant, &mut self.intern, ProofValueElision::None);
                result.map(|decl| Some(decl_to_constant_info(decl, constant.hints)))
            }
        }
    }

    /// Session-shared variant of [`convert_parsed_constant_to_type_stub`].
    pub fn type_stub(
        &mut self,
        constant: &ParsedConstant,
    ) -> Result<Option<clean_kernel::env::ConstantInfo>, ImportError> {
        if is_inductive_family_kind(&constant.kind) {
            return Ok(None);
        }
        let Some(type_raw) = constant.type_.as_ref() else {
            return Ok(None);
        };
        let (type_, _stats) = convert_expr(&constant.name, type_raw, &mut self.intern)?;
        let level_params = convert_level_params(&constant.level_params);
        let name = Name::interned(&constant.name);
        let kind = match constant.kind {
            ConstantKind::Opaque => KernelConstantKind::Opaque,
            _ => KernelConstantKind::Theorem,
        };
        Ok(Some(
            clean_kernel::env::ConstantInfo::new_with_reducibility(
                name,
                level_params,
                type_,
                None,
                clean_kernel::env::Reducibility::Opaque,
                kind,
            ),
        ))
    }
}

/// Convert a `ParsedConstant` to a VALUE-LESS trusted-import [`clean_kernel::env::ConstantInfo`]
/// using ONLY its type — for a value-less `Theorem`/`Opaque` (a proof body the
/// TYPES-ONLY loader skipped) that [`convert_parsed_constant_to_const_info`]
/// rejects with `MissingValue` (a non-elided theorem has no value to place).
///
/// The kernel NEVER δ-unfolds a `Theorem`/`Opaque` value, so a value-less stub is
/// a sound trusted import: it supplies the constant's TYPE — all a dependent's
/// type-check can consult — and carries no value to be trusted. The kind is kept
/// as `Theorem`/`Opaque` (NOT `Axiom`), so this never inflates the axiom set.
/// Returns `Ok(None)` for an inductive family or a type-less constant.
///
/// SOUNDNESS: registering a value-less stub for a trusted import cannot admit a
/// false proof — it adds only a TYPE. If that type is wrong, a dependent that
/// actually consults it fails its own `check_type`; it can never make an
/// ill-typed target pass. Intended for the per-constant walk, where the target
/// (the only constant `check_type`'d) is loaded WITH its value separately.
pub fn convert_parsed_constant_to_type_stub(
    constant: &ParsedConstant,
) -> Result<Option<clean_kernel::env::ConstantInfo>, ImportError> {
    ConstantConvertSession::default().type_stub(constant)
}

/// Convert a parsed constant to a ConvertedConstant.
///
/// The `intern` cache is shared across all constants in a module for
/// cross-constant expression deduplication (#2383).
#[inline]
pub(super) fn convert_parsed_constant(
    constant: &ParsedConstant,
    intern: &mut ExprInternCache,
    elide: ProofValueElision,
) -> ConvertedConstant {
    let name = constant.name.clone();
    match constant.kind {
        ConstantKind::Inductive => {
            let (result, stats) = convert_inductive_val(constant, intern);
            ConvertedConstant::Inductive(name, result, stats)
        }
        ConstantKind::Constructor => {
            let (result, stats) = convert_constructor_val(constant, intern);
            ConvertedConstant::Constructor(name, result, stats)
        }
        ConstantKind::Recursor => {
            let (result, stats) = convert_recursor_val_partial(constant, intern);
            ConvertedConstant::Recursor(name, result, stats)
        }
        _ => {
            let (result, stats) = convert_constant(constant, intern, elide);
            let result = result.map(|decl| {
                let fields = ExportFields {
                    hints: constant.hints,
                    all: constant.mutual_declarations.clone(),
                };
                (decl, fields)
            });
            ConvertedConstant::Other(name, result, stats)
        }
    }
}

/// Convert an inductive constant to InductiveVal
pub(super) fn convert_inductive_val(
    constant: &ParsedConstant,
    intern: &mut ExprInternCache,
) -> (Result<InductiveVal, ImportError>, ExprSharingStats) {
    let mut stats = ExprSharingStats::default();
    let result = (|| {
        let (type_, s) = constant
            .type_
            .as_ref()
            .ok_or_else(|| ImportError::MissingType(constant.name.clone()))
            .and_then(|t| convert_expr(&constant.name, t, intern))?;
        stats.merge(&s);

        let level_params: Vec<Name> = constant
            .level_params
            .iter()
            .map(|s| Name::interned(s))
            .collect();
        let name = Name::interned(&constant.name);

        let ind_data = constant.inductive_val.as_ref();

        // is_large_elim is recomputed after conversion using allows_large_elim()
        // with actual constructor types. Set a placeholder here; the fixup pass
        // in load_module_constants runs after all constants are converted.
        Ok(InductiveVal {
            name: name.clone(),
            level_params,
            type_,
            num_params: ind_data.map_or(0, |d| d.num_params),
            num_indices: ind_data.map_or(0, |d| d.num_indices),
            all_names: ind_data.map_or_else(
                || vec![name.clone()],
                |d| d.all.iter().map(|s| Name::interned(s)).collect(),
            ),
            constructor_names: ind_data
                .map(|d| d.ctors.iter().map(|s| Name::interned(s)).collect())
                .unwrap_or_default(),
            is_recursive: ind_data.is_some_and(|d| d.is_rec),
            is_reflexive: ind_data.is_some_and(|d| d.is_reflexive),
            is_large_elim: true, // placeholder, recomputed in fixup pass
            is_nested: ind_data.is_some_and(|d| d.is_nested),
        })
    })();
    (result, stats)
}

/// Convert a constructor constant to ConstructorVal
pub(super) fn convert_constructor_val(
    constant: &ParsedConstant,
    intern: &mut ExprInternCache,
) -> (Result<ConstructorVal, ImportError>, ExprSharingStats) {
    let mut stats = ExprSharingStats::default();
    let result = (|| {
        let (type_, s) = constant
            .type_
            .as_ref()
            .ok_or_else(|| ImportError::MissingType(constant.name.clone()))
            .and_then(|t| convert_expr(&constant.name, t, intern))?;
        stats.merge(&s);

        let level_params: Vec<Name> = constant
            .level_params
            .iter()
            .map(|s| Name::interned(s))
            .collect();
        let name = Name::interned(&constant.name);

        let ctor_data = constant.constructor_val.as_ref();

        Ok(ConstructorVal {
            name: name.clone(),
            inductive_name: ctor_data.map_or_else(
                || {
                    Name::interned(
                        constant
                            .name
                            .rsplit_once('.')
                            .map_or(constant.name.as_str(), |(p, _)| p),
                    )
                },
                |d| Name::interned(&d.induct),
            ),
            level_params,
            type_,
            num_params: ctor_data.map_or(0, |d| d.num_params),
            num_fields: ctor_data.map_or(0, |d| d.num_fields),
            constructor_idx: ctor_data.map_or(0, |d| d.cidx),
        })
    })();
    (result, stats)
}

/// Convert a recursor constant partially - recursive fields computed later
/// Infer the [`RecursorArgOrder`] for a recursor from its fully-qualified name.
///
/// The `.olean` Lean-4 `RecursorVal` layout does **not** store an explicit
/// argument-order discriminant — it is a Clean-kernel-specific field
/// ([`RecursorArgOrder`]) that materially affects iota-reduction (it decides
/// where the major premise sits in the application). On import we therefore
/// reconstruct it from the recursor's name, matching the kernel's own naming
/// convention in `inductive_recursor.rs`:
///
/// - `T.recOn` / `T.casesOn` (and their nested-inductive `_2`, `_3`, ...
///   variants) place the major premise immediately after the motives and
///   indices ([`RecursorArgOrder::MajorAfterMotive`]) — the Lean-faithful
///   layout the kernel's `add_inductive` generates for both.
/// - Every other recursor (`T.rec`, `T.brecOn`, `T.below`, ...) places the
///   major premise after the minor premises
///   ([`RecursorArgOrder::MajorAfterMinors`]).
///
/// This is the single source of truth shared by both import pipelines
/// (`convert_recursor_val_partial` and `convert_load_recursor_val`) so the two
/// paths can never silently diverge on `arg_order` for the same `.olean`.
///
/// # REQUIRES
/// - `name` is a recursor's fully-qualified constant name.
///
/// # ENSURES
/// - Returns `MajorAfterMotive` iff `name` is a `recOn`/`casesOn`-style
///   eliminator.
/// - Deterministic for a given `name`.
pub(crate) fn infer_recursor_arg_order(name: &str) -> RecursorArgOrder {
    if name.ends_with(".recOn")
        || name.contains(".recOn_")
        || name.ends_with(".casesOn")
        || name.contains(".casesOn_")
    {
        RecursorArgOrder::MajorAfterMotive
    } else {
        RecursorArgOrder::MajorAfterMinors
    }
}

pub(super) fn convert_recursor_val_partial(
    constant: &ParsedConstant,
    intern: &mut ExprInternCache,
) -> (
    Result<(RecursorVal, Vec<Name>, u32), ImportError>,
    ExprSharingStats,
) {
    let mut stats = ExprSharingStats::default();
    let result = (|| {
        let (type_, s) = constant
            .type_
            .as_ref()
            .ok_or_else(|| ImportError::MissingType(constant.name.clone()))
            .and_then(|t| convert_expr(&constant.name, t, intern))?;
        stats.merge(&s);

        let level_params: Vec<Name> = constant
            .level_params
            .iter()
            .map(|s| Name::interned(s))
            .collect();
        let name = Name::interned(&constant.name);

        let inductive_name = Name::interned(
            constant
                .name
                .strip_suffix(".rec")
                .or_else(|| constant.name.strip_suffix(".recOn"))
                .or_else(|| constant.name.strip_suffix(".casesOn"))
                .or_else(|| constant.name.strip_suffix(".brecOn"))
                .or_else(|| {
                    // A nested block's auxiliary `T.rec_<n>` belongs to `T`.
                    constant
                        .name
                        .rsplit_once('.')
                        .filter(|(_, suffix)| is_aux_recursor_suffix(suffix))
                        .map(|(parent, _)| parent)
                })
                .unwrap_or(&constant.name),
        );

        let rec_data = constant.recursor_val.as_ref();

        let mutual_inductives: Vec<Name> = rec_data.map_or_else(
            || vec![inductive_name.clone()],
            |d| d.all.iter().map(|s| Name::interned(s)).collect(),
        );

        let param_count = rec_data.map_or(0, |d| d.num_params);

        // Convert rules with placeholder recursive_fields (will be filled in later)
        let rules: Vec<RecursorRule> = rec_data
            .map(|d| {
                d.rules
                    .iter()
                    .map(|r| {
                        let rhs = match r.rhs.as_ref() {
                            Some(e) => {
                                let (rhs, s) = convert_expr(&constant.name, e, intern)?;
                                stats.merge(&s);
                                rhs
                            }
                            None => {
                                return Err(ImportError::ExprConversion {
                                    name: constant.name.clone(),
                                    message: format!(
                                        "recursor rule for {} has no RHS expression",
                                        r.ctor
                                    ),
                                });
                            }
                        };

                        Ok(RecursorRule {
                            constructor_name: Name::interned(&r.ctor),
                            num_fields: r.num_fields,
                            recursive_fields: vec![], // Placeholder, filled in later
                            rhs,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .transpose()?
            .unwrap_or_default();

        let arg_order = infer_recursor_arg_order(&constant.name);

        let rec_val = RecursorVal {
            name: name.clone(),
            arg_order,
            level_params,
            type_,
            inductive_name,
            num_params: param_count,
            num_indices: rec_data.map_or(0, |d| d.num_indices),
            num_motives: rec_data.map_or(1, |d| d.num_motives),
            num_minors: rec_data.map_or(0, |d| d.num_minors),
            rules,
            is_k: rec_data.is_some_and(|d| d.k),
        };

        Ok((rec_val, mutual_inductives, param_count))
    })();
    (result, stats)
}

fn convert_constant(
    constant: &ParsedConstant,
    intern: &mut ExprInternCache,
    elide: ProofValueElision,
) -> (Result<Declaration, ImportError>, ExprSharingStats) {
    let mut stats = ExprSharingStats::default();
    let result = (|| {
        let (type_, s) = constant
            .type_
            .as_ref()
            .ok_or_else(|| ImportError::MissingType(constant.name.clone()))
            .and_then(|t| convert_expr(&constant.name, t, intern))?;
        stats.merge(&s);

        // Conversion-time proof-value elision (#6 memory lever): for elided proof
        // kinds that ACTUALLY have a value, never build/intern the value DAG — this
        // removes the peak the post-hoc null could not reclaim (interned `Arc`s keep
        // it resident). The TYPE is always built. Gating on `value.is_some()` keeps
        // the registered-constant SET identical to the post-hoc-null baseline: a
        // value-less Theorem/Opaque still hits `MissingValue` (skipped) rather than
        // being newly registered via a placeholder. The `Sort 0` placeholder below is
        // therefore only ever substituted for a real value we skipped, and is dropped
        // to `None` by the post-hoc null — so the env value=None set is unchanged.
        let should_elide = constant.value.is_some() && elides_value(elide, &constant.kind);
        let value = if should_elide {
            None
        } else {
            match &constant.value {
                Some(v) => {
                    let (val, s) = convert_expr(&constant.name, v, intern)?;
                    stats.merge(&s);
                    Some(val)
                }
                None => None,
            }
        };

        let level_params = convert_level_params(&constant.level_params);
        let name = Name::interned(&constant.name);

        match constant.kind {
            ConstantKind::Axiom | ConstantKind::Quot => Ok(Declaration::Axiom {
                name,
                level_params,
                type_,
            }),
            ConstantKind::Definition => {
                let value =
                    value.ok_or_else(|| ImportError::MissingValue(constant.name.clone()))?;
                // Derive is_reducible from hints if available; default false when unknown
                let is_reducible = matches!(constant.hints, Some(ReducibilityHintsData::Abbrev));
                Ok(Declaration::Definition {
                    name,
                    level_params,
                    type_,
                    value,
                    is_reducible,
                })
            }
            ConstantKind::Theorem => {
                let value = proof_value_or_placeholder(value, should_elide, &constant.name)?;
                Ok(Declaration::Theorem {
                    name,
                    level_params,
                    type_,
                    value,
                })
            }
            ConstantKind::Opaque => {
                let value = proof_value_or_placeholder(value, should_elide, &constant.name)?;
                Ok(Declaration::Opaque {
                    name,
                    level_params,
                    type_,
                    value,
                })
            }
            // Inductive-related constants are now handled by try_register_* functions
            // This branch should not be reached from normal code path, but kept for safety
            ConstantKind::Inductive | ConstantKind::Constructor | ConstantKind::Recursor => {
                Ok(Declaration::Axiom {
                    name,
                    level_params,
                    type_,
                })
            }
        }
    })();
    (result, stats)
}

/// Check if a type mentions any inductive in the given list.
/// `rec_<n>` (n ≥ 1 digits): the suffix Lean gives a nested block's auxiliary
/// recursors.
pub(crate) fn is_aux_recursor_suffix(suffix: &str) -> bool {
    suffix
        .strip_prefix("rec_")
        .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

pub(super) fn type_mentions_any_inductive(expr: &Expr, inductive_names: &[Name]) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => inductive_names.contains(name),
        ExprKind::App(f, a) => {
            type_mentions_any_inductive(f, inductive_names)
                || type_mentions_any_inductive(a, inductive_names)
        }
        ExprKind::Pi(_, domain, codomain) | ExprKind::Lam(_, domain, codomain) => {
            type_mentions_any_inductive(domain, inductive_names)
                || type_mentions_any_inductive(codomain, inductive_names)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            type_mentions_any_inductive(ty, inductive_names)
                || type_mentions_any_inductive(val, inductive_names)
                || type_mentions_any_inductive(body, inductive_names)
        }
        ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) | ExprKind::Squash(e) => {
            type_mentions_any_inductive(e, inductive_names)
        }
        _ => false,
    }
}

/// Compute recursive field flags for a constructor type.
///
/// A field is recursive if its domain mentions any inductive from the mutual group.
pub(super) fn recursive_field_flags_from_ctor(
    ctor_ty: &Expr,
    inductive_names: &[Name],
    num_params: u32,
) -> Vec<bool> {
    let mut flags = Vec::new();
    // Walk the constructor type's binder spine by reference. The loop only reads
    // `domain` (already borrowed) and descends `codomain`; it never mutates or
    // returns the cursor, so walking the borrowed `Arc<Expr>` children yields the
    // exact same `flags` while avoiding an `Expr` clone per Pi step.
    let mut current: &Expr = ctor_ty;
    let mut arg_idx = 0u32;

    while let ExprKind::Pi(_, domain, codomain) = current.kind() {
        if arg_idx >= num_params {
            flags.push(type_mentions_any_inductive(domain, inductive_names));
        }
        current = codomain;
        arg_idx += 1;
    }

    flags
}

/// Derive recursive field flags for a constructor using environment data.
pub(super) fn compute_recursive_fields_from_env(
    env: &clean_kernel::env::Environment,
    ctor_name: &Name,
    inductive_names: &[Name],
    num_params: u32,
    num_fields_hint: u32,
) -> Vec<bool> {
    if let Some(ctor_val) = env.get_constructor(ctor_name) {
        let mut flags =
            recursive_field_flags_from_ctor(&ctor_val.type_, inductive_names, num_params);
        flags.resize(num_fields_hint as usize, false);
        flags
    } else {
        vec![false; num_fields_hint as usize]
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod proof_arc_elision_tests;
