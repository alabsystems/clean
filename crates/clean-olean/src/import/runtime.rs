// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Owned declaration content from captured .olean parts, without registration.
//!
//! This is a computational-content transport, not a kernel check, dependency
//! closure, source refinement, executable IR, or permission to unfold partial
//! definitions. Every supplied part and every constants-array slot is retained.
//! Parts are cumulative snapshots: equal Names across parts are not deduplicated.
//! Imports, persistent extensions, native code and IR extensions are outside this
//! API; captured bytes remain available for those independent consumers.
//!
//! Expressions use the existing direct core-Expr reader (including its bounded
//! conversion and supported-format policy). Binder display names are alpha-erased.
//! MData payloads are carried losslessly since 2026-09-30 (`region/mdata.rs`);
//! one the reader cannot decode refuses the expression, which is an issue here. A
//! decoded body is never evidence that all declaration metadata was understood.

use super::convert_expr_direct::{read_and_convert_expr_with_memo, RegionPtrCache};
use super::load_parse::{parse_runtime_module, parse_runtime_module_incremental, LoadConstant};
use super::ExprInternCache;
use crate::module::{ConstantKind, DefinitionSafety, ReducibilityHintsData};
use crate::region::CompactedRegion;
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::name::Name;
use std::collections::{BTreeSet, HashSet};
use std::sync::Arc;

/// Explicit captured input; a label is provenance, never a module identity.
#[derive(Clone, Debug)]
pub struct RuntimeOleanInput {
    pub label: String,
    pub bytes: Arc<[u8]>,
}

/// Limits on bytes copied into a parser region for one captured module.
/// The caller already owns the `RuntimeOleanInput` buffers; these limits do
/// not bound acquisition of those buffers or grant import authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RuntimeExtractionLimits {
    pub max_part_bytes: usize,
    pub max_captured_bytes: usize,
}

impl Default for RuntimeExtractionLimits {
    fn default() -> Self {
        Self {
            max_part_bytes: 256 * 1024 * 1024,
            max_captured_bytes: 512 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuntimeOleanPart {
    Base,
    Server,
    Private,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuntimePartIdentity {
    pub part: RuntimeOleanPart,
    pub label: String,
    pub byte_count: usize,
    pub blake3: [u8; 32],
}

/// The complete ordered prefix is part of each row's provenance. Identical
/// private bytes can resolve differently against different captured base bytes.
#[derive(Clone, Debug)]
pub struct RuntimePartExtraction {
    pub identity: RuntimePartIdentity,
    pub captured: RuntimeOleanInput,
    pub borrowed_prefix: Vec<RuntimePartIdentity>,
    /// Unknown when the envelope/array itself could not be decoded.
    pub source_row_count: Option<usize>,
    pub rows: Vec<RuntimeDeclarationRow>,
    pub error: Option<String>,
}

#[derive(Clone, Debug)]
pub struct RuntimeDeclarationRow {
    pub index: usize,
    /// Metadata failure retains the slot and message, not a fabricated Name.
    pub declaration: Result<RuntimeDeclaration, String>,
}

#[derive(Clone, Debug)]
pub enum RuntimeBody {
    /// Includes an opaque's stored value; this does not grant unfold permission.
    Stored(Result<Expr, String>),
    /// Axioms may be public/private stubs supplied at another level. This is
    /// deliberately not called an absent runtime implementation or a safe body.
    NoStoredValueForKind,
    MissingRequiredValue,
}

#[derive(Clone, Debug)]
pub struct RuntimeRecursorRule {
    pub constructor: Name,
    pub num_fields: u32,
    pub rhs: Result<Expr, String>,
}

#[derive(Clone, Debug)]
pub enum RuntimeFamily {
    None,
    Inductive {
        all: Vec<Name>,
        constructors: Vec<Name>,
        num_params: u32,
        num_indices: u32,
        num_nested: Option<u64>,
        is_nested: bool,
        is_recursive: bool,
        is_unsafe: bool,
        is_reflexive: bool,
    },
    Constructor {
        inductive: Name,
        index: u32,
        num_params: u32,
        num_fields: u32,
        is_unsafe: bool,
    },
    Recursor {
        all: Vec<Name>,
        num_params: u32,
        num_indices: u32,
        num_motives: u32,
        num_minors: u32,
        k: bool,
        is_unsafe: bool,
        rules: Vec<RuntimeRecursorRule>,
    },
    /// The current load metadata reader does not preserve QuotKind. Never
    /// silently project it to one of the five primitive quotient operations.
    UnsupportedQuotientMetadata,
}

#[derive(Clone, Debug)]
pub struct RuntimeDeclaration {
    pub name: Name,
    pub kind: ConstantKind,
    pub level_params: Vec<Name>,
    pub declaration_safety: Option<DefinitionSafety>,
    pub hints: Option<ReducibilityHintsData>,
    /// Exact mutual group on definition/theorem/opaque values. None on an
    /// applicable kind means the legacy format did not carry this field.
    pub mutual_declarations: Option<Vec<Name>>,
    pub type_: Result<Expr, String>,
    pub body: RuntimeBody,
    pub family: RuntimeFamily,
    /// Sorted exact typed references from type, stored body, all recursor RHS,
    /// projection owners and family Name fields. Self references are retained.
    pub dependencies: BTreeSet<Name>,
    /// False on any incomplete field.
    /// Never means dependency closure or successful kernel admission.
    pub represented_fields_complete: bool,
    pub issues: Vec<String>,
}

/// Decode every supplied part in order without looking up any dependency or
/// mutating an Environment. A missing optional companion is not a malformed
/// present part. Callers must supply all captured parts needed by pointers.
///
/// Hard inherited limits: at most 1,000,000 rows/part, 10,000 recursor rules,
/// 100 MB incremental address gap, and the direct reader's conversion budget.
/// The default capture limit is 256 MiB/part and 512 MiB across supplied parts.
/// This is not an OS memory limit: callers must still bound input acquisition.
pub fn extract_olean_runtime_parts(
    base: RuntimeOleanInput,
    server: Option<RuntimeOleanInput>,
    private: Option<RuntimeOleanInput>,
) -> Vec<RuntimePartExtraction> {
    extract_olean_runtime_parts_with_limits(
        base,
        server,
        private,
        RuntimeExtractionLimits::default(),
    )
}

/// Like [`extract_olean_runtime_parts`], with caller-selected capture limits.
/// An over-budget part and every part borrowing it retain their captures and
/// report an error with an unknown row count; neither becomes an empty census.
pub fn extract_olean_runtime_parts_with_limits(
    base: RuntimeOleanInput,
    server: Option<RuntimeOleanInput>,
    private: Option<RuntimeOleanInput>,
    limits: RuntimeExtractionLimits,
) -> Vec<RuntimePartExtraction> {
    let inputs = [
        (RuntimeOleanPart::Base, Some(&base)),
        (RuntimeOleanPart::Server, server.as_ref()),
        (RuntimeOleanPart::Private, private.as_ref()),
    ];
    let mut prefix = Vec::new();
    let mut output = Vec::new();
    let mut captured_bytes = 0usize;
    let mut capture_error = None;
    for (part, input) in inputs {
        let Some(input) = input else { continue };
        let identity = RuntimePartIdentity {
            part,
            label: input.label.clone(),
            byte_count: input.bytes.len(),
            blake3: *blake3::hash(&input.bytes).as_bytes(),
        };
        if capture_error.is_none() {
            captured_bytes = match captured_bytes.checked_add(input.bytes.len()) {
                Some(size) => size,
                None => {
                    capture_error = Some("runtime captured byte count overflow".into());
                    captured_bytes
                }
            };
            if input.bytes.len() > limits.max_part_bytes {
                capture_error = Some(format!(
                    "runtime part has {} bytes, limit is {}",
                    input.bytes.len(),
                    limits.max_part_bytes
                ));
            } else if captured_bytes > limits.max_captured_bytes {
                capture_error = Some(format!(
                    "runtime captured prefix has {captured_bytes} bytes, limit is {}",
                    limits.max_captured_bytes
                ));
            }
        }
        let mut result = RuntimePartExtraction {
            identity: identity.clone(),
            captured: input.clone(),
            borrowed_prefix: prefix.clone(),
            source_row_count: None,
            rows: Vec::new(),
            error: capture_error.clone(),
        };
        let parsed = if result.error.is_none() {
            Some(match part {
                RuntimeOleanPart::Base => parse_runtime_module(input.bytes.to_vec()),
                RuntimeOleanPart::Server => {
                    parse_runtime_module_incremental(&base.bytes, None, input.bytes.to_vec())
                }
                RuntimeOleanPart::Private => parse_runtime_module_incremental(
                    &base.bytes,
                    server.as_ref().map(|value| value.bytes.as_ref()),
                    input.bytes.to_vec(),
                ),
            })
        } else {
            None
        };
        match parsed {
            Some(Ok(module)) => match &module.runtime_rows {
                Some(rows) => {
                    result.source_row_count = Some(rows.len());
                    let region = module.region();
                    // Never share pointer memo entries between part captures.
                    let mut intern = ExprInternCache::with_capacity(1024);
                    let mut memo = RegionPtrCache::for_region();
                    for (index, row) in rows.iter().enumerate() {
                        result.rows.push(RuntimeDeclarationRow {
                            index,
                            declaration: row
                                .as_ref()
                                .map_err(Clone::clone)
                                .map(|row| decode_row(row, &region, &mut intern, &mut memo)),
                        });
                    }
                }
                None => result.error = Some("runtime population was not captured".into()),
            },
            Some(Err(error)) => result.error = Some(error.to_string()),
            None => {}
        }
        prefix.push(identity);
        output.push(result);
    }
    output
}

fn decode_expr(
    ptr: u64,
    row: &LoadConstant,
    region: &CompactedRegion<'_>,
    intern: &mut ExprInternCache,
    memo: &mut RegionPtrCache,
) -> Result<Expr, String> {
    if ptr == 0 {
        return Err("required expression is absent".into());
    }
    read_and_convert_expr_with_memo(region, ptr, &row.name, intern, memo)
        .map(|(expr, _)| expr)
        .map_err(|error| error.to_string())
}

fn decode_row(
    row: &LoadConstant,
    region: &CompactedRegion<'_>,
    intern: &mut ExprInternCache,
    memo: &mut RegionPtrCache,
) -> RuntimeDeclaration {
    let mut issues = Vec::new();
    let mut dependencies = BTreeSet::new();
    if let Some(all) = &row.runtime_mutual {
        dependencies.extend(all.iter().cloned());
    } else if matches!(
        row.kind,
        ConstantKind::Definition | ConstantKind::Theorem | ConstantKind::Opaque
    ) {
        issues.push("mutual group metadata is not represented by this legacy format".into());
    }
    let type_ = decode_expr(row.type_ptr, row, region, intern, memo);
    record_expr(&type_, "type", &mut dependencies, &mut issues);
    let needs_value = matches!(
        row.kind,
        ConstantKind::Definition | ConstantKind::Theorem | ConstantKind::Opaque
    );
    let body = if needs_value && row.value_ptr == 0 {
        issues.push("missing required stored declaration value".into());
        RuntimeBody::MissingRequiredValue
    } else if needs_value {
        let value = decode_expr(row.value_ptr, row, region, intern, memo);
        record_expr(&value, "value", &mut dependencies, &mut issues);
        RuntimeBody::Stored(value)
    } else {
        RuntimeBody::NoStoredValueForKind
    };
    let family = if let Some(value) = &row.inductive_val {
        if row.num_nested.is_none() {
            issues.push("legacy nested-family flag does not represent exact nested count".into());
        }
        dependencies.extend(row.kernel_all.iter().cloned());
        dependencies.extend(row.kernel_ctors.iter().cloned());
        RuntimeFamily::Inductive {
            all: row.kernel_all.clone(),
            constructors: row.kernel_ctors.clone(),
            num_params: value.num_params,
            num_indices: value.num_indices,
            num_nested: row.num_nested,
            is_nested: value.is_nested,
            is_recursive: value.is_rec,
            is_unsafe: value.is_unsafe,
            is_reflexive: value.is_reflexive,
        }
    } else if let Some(value) = &row.constructor_val {
        if let Some(inductive) = &row.kernel_inductive {
            dependencies.insert(inductive.clone());
            RuntimeFamily::Constructor {
                inductive: inductive.clone(),
                index: value.cidx,
                num_params: value.num_params,
                num_fields: value.num_fields,
                is_unsafe: value.is_unsafe,
            }
        } else {
            issues.push("constructor owner is absent".into());
            RuntimeFamily::None
        }
    } else if let Some(value) = &row.recursor_val {
        dependencies.extend(value.all.iter().cloned());
        let mut rules = Vec::new();
        for rule in &value.rules {
            dependencies.insert(rule.ctor.clone());
            let rhs = decode_expr(rule.rhs_ptr, row, region, intern, memo);
            record_expr(&rhs, "recursor RHS", &mut dependencies, &mut issues);
            rules.push(RuntimeRecursorRule {
                constructor: rule.ctor.clone(),
                num_fields: rule.num_fields,
                rhs,
            });
        }
        RuntimeFamily::Recursor {
            all: value.all.clone(),
            num_params: value.num_params,
            num_indices: value.num_indices,
            num_motives: value.num_motives,
            num_minors: value.num_minors,
            k: value.k,
            is_unsafe: value.is_unsafe,
            rules,
        }
    } else if row.kind == ConstantKind::Quot {
        issues.push("quotient operation metadata is not represented".into());
        RuntimeFamily::UnsupportedQuotientMetadata
    } else {
        RuntimeFamily::None
    };
    RuntimeDeclaration {
        name: row.kernel_name.clone(),
        kind: row.kind.clone(),
        level_params: row.kernel_level_params.clone(),
        declaration_safety: row.definition_safety,
        hints: row.hints,
        mutual_declarations: row.runtime_mutual.clone(),
        type_,
        body,
        family,
        dependencies,
        represented_fields_complete: issues.is_empty(),
        issues,
    }
}

fn record_expr(
    expr: &Result<Expr, String>,
    field: &str,
    dependencies: &mut BTreeSet<Name>,
    issues: &mut Vec<String>,
) {
    let expr = match expr {
        Ok(expr) => expr,
        Err(error) => {
            issues.push(format!("{field}: {error}"));
            return;
        }
    };
    let mut pending = vec![expr];
    let mut seen = HashSet::new();
    while let Some(expr) = pending.pop() {
        // Address identity is used only to visit a live owned DAG once; no
        // pointer dereference or cross-capture cache is involved.
        if !seen.insert(expr as *const Expr) {
            continue;
        }
        if seen.len() > 1_000_000 {
            issues.push(format!("{field}: dependency traversal limit exceeded"));
            break;
        }
        match expr.kind() {
            ExprKind::Const(name, _) => {
                dependencies.insert(name.clone());
            }
            ExprKind::App(a, b) | ExprKind::Lam(_, a, b) | ExprKind::Pi(_, a, b) => {
                pending.extend([a.as_ref(), b.as_ref()])
            }
            ExprKind::Let(_, ty, value, body, _) => {
                pending.extend([ty.as_ref(), value.as_ref(), body.as_ref()])
            }
            ExprKind::Proj(owner, _, inner) => {
                dependencies.insert(owner.clone());
                pending.push(inner);
            }
            ExprKind::MData(_, inner) => pending.push(inner),
            ExprKind::BVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => {}
            _ => issues.push(format!(
                "{field}: unsupported non-core expression dependency form"
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn projection_owner_and_body_references_are_both_preserved() {
        let owner = Name::anon().str("Quoted.Owner");
        let value = Name::anon().str("Quoted").str("Owner");
        let expression = Ok(Expr::proj(
            owner.clone(),
            0,
            Expr::const_(value.clone(), vec![]),
        ));
        let mut dependencies = BTreeSet::new();
        let mut issues = Vec::new();
        record_expr(&expression, "value", &mut dependencies, &mut issues);
        assert_eq!(dependencies, [owner, value].into_iter().collect());
        assert!(issues.is_empty());
    }
    /// The direct reader carries Lean's mdata payload exactly, so an mdata
    /// node no longer makes a field incomplete; its inner term is still walked.
    #[test]
    fn carried_mdata_payload_is_complete_content() {
        let expression = Ok(Expr::mdata(
            vec![(
                Name::anon().str("borrowed"),
                clean_kernel::expr::MDataValue::Bool(true),
            )],
            Expr::const_(Name::anon().str("Nat"), vec![]),
        ));
        let mut dependencies = BTreeSet::new();
        let mut issues = Vec::new();
        record_expr(&expression, "value", &mut dependencies, &mut issues);
        assert!(issues.is_empty(), "{issues:?}");
        assert_eq!(
            dependencies,
            [Name::anon().str("Nat")].into_iter().collect()
        );
    }

    /// An expression the reader refused (e.g. an mdata payload it cannot
    /// decode) is an issue, never complete content.
    #[test]
    fn refused_expression_is_an_issue() {
        let expression = Err("mdata: unknown DataValue constructor (tag 9, 1 fields)".into());
        let mut dependencies = BTreeSet::new();
        let mut issues = Vec::new();
        record_expr(&expression, "value", &mut dependencies, &mut issues);
        assert_eq!(issues.len(), 1);
        assert!(issues[0].contains("mdata"));
    }
}
