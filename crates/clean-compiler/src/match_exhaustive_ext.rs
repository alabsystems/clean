// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Method's &self is intentionally retained; recursive call goes through self for future state.
#![allow(clippy::only_used_in_recursion)]

//! Extended match exhaustiveness checking for compiler IR.
//!
//! Bridges `IRAlt`/`IRType`/`IRLiteral`/`CtorInfo` to the Maranget usefulness
//! algorithm with configurable missing-pattern, redundancy, and unreachability
//! analysis. Based on Maranget, "Warnings for Pattern Matching" (JFP 2007).
//!
//! Part of #3084 - Match expression compilation for native execution.

use std::collections::{HashMap, HashSet};

use clean_kernel::Name;

use crate::ir::{CtorInfo, IRAlt, IRLiteral, IRType};

/// Configuration for extended exhaustiveness analysis.
#[derive(Debug, Clone)]
pub(crate) struct ExhaustivenessConfig {
    /// Maximum depth for nested pattern analysis (default: 10).
    pub max_pattern_depth: usize,
    /// Whether to report guard-dependent arms as potentially non-exhaustive.
    pub check_guards: bool,
    /// Whether to compute and report missing patterns.
    pub report_missing_patterns: bool,
    /// Whether to detect redundant arms.
    pub check_redundancy: bool,
}

impl Default for ExhaustivenessConfig {
    fn default() -> Self {
        Self {
            max_pattern_depth: 10,
            check_guards: false,
            report_missing_patterns: true,
            check_redundancy: true,
        }
    }
}

/// A human-readable pattern description for diagnostics.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub(crate) enum PatternDesc {
    /// Constructor pattern with fields.
    Ctor {
        name: Name,
        fields: Vec<PatternDesc>,
    },
    /// Wildcard (matches anything).
    Wildcard,
    /// Literal value.
    Literal(IRLiteral),
    /// Or-pattern (any of the alternatives).
    Or(Vec<PatternDesc>),
}

impl PartialEq for PatternDesc {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                PatternDesc::Ctor {
                    name: n1,
                    fields: f1,
                },
                PatternDesc::Ctor {
                    name: n2,
                    fields: f2,
                },
            ) => n1 == n2 && f1 == f2,
            (PatternDesc::Wildcard, PatternDesc::Wildcard) => true,
            (PatternDesc::Literal(a), PatternDesc::Literal(b)) => {
                LitKey::from_ir(a) == LitKey::from_ir(b)
            }
            (PatternDesc::Or(a), PatternDesc::Or(b)) => a == b,
            _ => false,
        }
    }
}

/// Result of extended exhaustiveness analysis.
#[derive(Debug, Clone)]
pub(crate) struct ExhaustivenessResult {
    /// Whether the match is exhaustive.
    pub is_exhaustive: bool,
    /// Patterns not covered by any arm.
    pub missing_patterns: Vec<PatternDesc>,
    /// Indices of fully redundant arms (subsumed by earlier arms).
    pub redundant_arms: Vec<usize>,
    /// Unreachable arm indices (== redundant without guards).
    pub unreachable_arms: Vec<usize>,
}

impl ExhaustivenessResult {
    fn exhaustive() -> Self {
        Self {
            is_exhaustive: true,
            missing_patterns: Vec::new(),
            redundant_arms: Vec::new(),
            unreachable_arms: Vec::new(),
        }
    }
}

// -- Internal pattern representation for the matrix algorithm -----------------

#[derive(Debug, Clone, PartialEq)]
enum Pat {
    Ctor {
        name: Name,
        tag: u32,
        args: Vec<Pat>,
    },
    Wild,
    Lit(LitKey),
    Or(Vec<Pat>),
}

/// Hashable literal key for specialization (floats use bit repr).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum LitKey {
    Bool(bool),
    UInt8(u8),
    UInt16(u16),
    UInt32(u32),
    UInt64(u64),
    USize(u64),
    NatBig(u128),
    Float32(u32),
    Float64(u64),
}

impl LitKey {
    fn from_ir(lit: &IRLiteral) -> Self {
        match lit {
            IRLiteral::Bool(b) => LitKey::Bool(*b),
            IRLiteral::UInt8(v) => LitKey::UInt8(*v),
            IRLiteral::UInt16(v) => LitKey::UInt16(*v),
            IRLiteral::UInt32(v) => LitKey::UInt32(*v),
            IRLiteral::UInt64(v) => LitKey::UInt64(*v),
            IRLiteral::USize(v) => LitKey::USize(*v as u64),
            IRLiteral::NatBig(v) => LitKey::NatBig(*v),
            IRLiteral::Float32(v) => LitKey::Float32(v.to_bits()),
            IRLiteral::Float64(v) => LitKey::Float64(v.to_bits()),
        }
    }

    fn to_string_key(&self) -> String {
        match self {
            LitKey::Bool(b) => format!("__lit_bool_{b}"),
            LitKey::UInt8(v) => format!("__lit_u8_{v}"),
            LitKey::UInt16(v) => format!("__lit_u16_{v}"),
            LitKey::UInt32(v) => format!("__lit_u32_{v}"),
            LitKey::UInt64(v) => format!("__lit_u64_{v}"),
            LitKey::USize(v) => format!("__lit_usize_{v}"),
            LitKey::NatBig(v) => format!("__lit_natbig_{v}"),
            LitKey::Float32(bits) => format!("__lit_f32_{bits}"),
            LitKey::Float64(bits) => format!("__lit_f64_{bits}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Head {
    Ctor(Name, u32, usize), // name, tag, arity
    Lit(LitKey),
}

// -- Public API ---------------------------------------------------------------

/// Check exhaustiveness of IR match alternatives with full configuration.
#[must_use]
pub(crate) fn check_exhaustiveness_ext(
    alts: &[IRAlt],
    _scrutinee_type: &IRType,
    ctor_info: &[CtorInfo],
    config: &ExhaustivenessConfig,
) -> ExhaustivenessResult {
    if alts.is_empty() {
        let missing = if config.report_missing_patterns {
            ctor_info
                .iter()
                .map(|ci| PatternDesc::Ctor {
                    name: ci.name.clone(),
                    fields: vec![PatternDesc::Wildcard; ci.field_types.len()],
                })
                .collect()
        } else {
            Vec::new()
        };
        return ExhaustivenessResult {
            is_exhaustive: false,
            missing_patterns: missing,
            redundant_arms: Vec::new(),
            unreachable_arms: Vec::new(),
        };
    }
    let matrix = build_pattern_matrix(alts);
    let all_ctors = build_ctor_set(ctor_info);
    let mut result = ExhaustivenessResult::exhaustive();
    if useful(&matrix, &[Pat::Wild], &all_ctors, config.max_pattern_depth) {
        result.is_exhaustive = false;
        if config.report_missing_patterns {
            result.missing_patterns = find_missing_patterns(alts, ctor_info);
        }
    }
    if config.check_redundancy {
        result.redundant_arms = find_redundant_arms_internal(&matrix, &all_ctors, config);
        result.unreachable_arms = result.redundant_arms.clone();
    }
    result
}

/// Check exhaustiveness with default configuration.
#[must_use]
pub(crate) fn check_exhaustiveness_ext_default(
    alts: &[IRAlt],
    scrutinee_type: &IRType,
    ctor_info: &[CtorInfo],
) -> ExhaustivenessResult {
    check_exhaustiveness_ext(
        alts,
        scrutinee_type,
        ctor_info,
        &ExhaustivenessConfig::default(),
    )
}

/// Compute which constructors are not covered by the alternatives.
#[must_use]
pub(crate) fn find_missing_patterns(alts: &[IRAlt], ctor_info: &[CtorInfo]) -> Vec<PatternDesc> {
    let covered: HashSet<u32> = alts.iter().map(|a| a.ctor.tag).collect();
    ctor_info
        .iter()
        .filter(|ci| !covered.contains(&ci.tag))
        .map(|ci| PatternDesc::Ctor {
            name: ci.name.clone(),
            fields: vec![PatternDesc::Wildcard; ci.field_types.len()],
        })
        .collect()
}

/// Find indices of redundant arms using the usefulness algorithm.
#[must_use]
pub(crate) fn find_redundant_arms(alts: &[IRAlt]) -> Vec<usize> {
    let matrix = build_pattern_matrix(alts);
    find_redundant_arms_internal(&matrix, &HashMap::new(), &ExhaustivenessConfig::default())
}

/// Maranget's U(P, q): is `new_row` useful w.r.t. `matrix`?
#[must_use]
pub(crate) fn pattern_matrix_useful(matrix: &[Vec<PatternDesc>], new_row: &[PatternDesc]) -> bool {
    let int_m: Vec<Vec<Pat>> = matrix
        .iter()
        .map(|r| r.iter().map(desc_to_pat).collect())
        .collect();
    let int_r: Vec<Pat> = new_row.iter().map(desc_to_pat).collect();
    useful(&int_m, &int_r, &HashMap::new(), 10)
}

/// Expand or-patterns into a flat list of alternatives.
#[must_use]
pub(crate) fn expand_or_patterns(pattern: &PatternDesc) -> Vec<PatternDesc> {
    match pattern {
        PatternDesc::Or(alts) => alts.iter().flat_map(expand_or_patterns).collect(),
        PatternDesc::Ctor { name, fields } => {
            let expanded: Vec<Vec<PatternDesc>> = fields.iter().map(expand_or_patterns).collect();
            let mut results = vec![Vec::new()];
            for field_alts in &expanded {
                let mut next = Vec::new();
                for partial in &results {
                    for alt in field_alts {
                        let mut row = partial.clone();
                        row.push(alt.clone());
                        next.push(row);
                    }
                }
                results = next;
            }
            results
                .into_iter()
                .map(|fs| PatternDesc::Ctor {
                    name: name.clone(),
                    fields: fs,
                })
                .collect()
        }
        PatternDesc::Wildcard | PatternDesc::Literal(_) => vec![pattern.clone()],
    }
}

// -- Internal helpers ---------------------------------------------------------

fn build_pattern_matrix(alts: &[IRAlt]) -> Vec<Vec<Pat>> {
    alts.iter()
        .map(|alt| {
            vec![Pat::Ctor {
                name: alt.ctor.name.clone(),
                tag: alt.ctor.tag,
                args: vec![Pat::Wild; alt.ctor.field_types.len()],
            }]
        })
        .collect()
}

fn build_ctor_set(ctor_info: &[CtorInfo]) -> HashMap<Name, (u32, usize)> {
    ctor_info
        .iter()
        .map(|ci| (ci.name.clone(), (ci.tag, ci.field_types.len())))
        .collect()
}

fn useful(
    matrix: &[Vec<Pat>],
    vector: &[Pat],
    all_ctors: &HashMap<Name, (u32, usize)>,
    depth: usize,
) -> bool {
    if depth == 0 {
        return false;
    }
    if vector.is_empty() {
        return matrix.is_empty();
    }
    match &vector[0] {
        Pat::Ctor { name, tag, args } => {
            let spec_m = specialize(matrix, name, *tag, args.len());
            let mut spec_v = args.clone();
            spec_v.extend_from_slice(&vector[1..]);
            useful(&spec_m, &spec_v, all_ctors, depth - 1)
        }
        Pat::Lit(key) => useful(
            &specialize_lit(matrix, key),
            &vector[1..],
            all_ctors,
            depth - 1,
        ),
        Pat::Or(alts) => alts.iter().any(|alt| {
            let mut v = vec![alt.clone()];
            v.extend_from_slice(&vector[1..]);
            useful(matrix, &v, all_ctors, depth)
        }),
        Pat::Wild => {
            let sigma = first_column_heads(matrix);
            if is_sigma_complete(&sigma, all_ctors) {
                sigma.iter().any(|head| match head {
                    Head::Ctor(name, tag, arity) => {
                        let spec_m = specialize(matrix, name, *tag, *arity);
                        let mut spec_v = vec![Pat::Wild; *arity];
                        spec_v.extend_from_slice(&vector[1..]);
                        useful(&spec_m, &spec_v, all_ctors, depth - 1)
                    }
                    Head::Lit(key) => useful(
                        &specialize_lit(matrix, key),
                        &vector[1..],
                        all_ctors,
                        depth - 1,
                    ),
                })
            } else {
                useful(&default_matrix(matrix), &vector[1..], all_ctors, depth - 1)
            }
        }
    }
}

fn specialize(matrix: &[Vec<Pat>], head: &Name, tag: u32, arity: usize) -> Vec<Vec<Pat>> {
    let mut out = Vec::new();
    for row in matrix {
        if row.is_empty() {
            continue;
        }
        specialize_pat(&row[0], &row[1..], head, tag, arity, &mut out);
    }
    out
}

fn specialize_pat(
    pat: &Pat,
    tail: &[Pat],
    head: &Name,
    tag: u32,
    arity: usize,
    out: &mut Vec<Vec<Pat>>,
) {
    match pat {
        Pat::Ctor { name, args, .. } if name == head => {
            let mut row = args.clone();
            row.extend_from_slice(tail);
            out.push(row);
        }
        Pat::Wild => {
            let mut row = vec![Pat::Wild; arity];
            row.extend_from_slice(tail);
            out.push(row);
        }
        Pat::Or(alts) => {
            for alt in alts {
                specialize_pat(alt, tail, head, tag, arity, out);
            }
        }
        _ => {}
    }
}

fn specialize_lit(matrix: &[Vec<Pat>], key: &LitKey) -> Vec<Vec<Pat>> {
    let mut out = Vec::new();
    for row in matrix {
        if row.is_empty() {
            continue;
        }
        match &row[0] {
            Pat::Lit(k) if k == key => out.push(row[1..].to_vec()),
            Pat::Wild => out.push(row[1..].to_vec()),
            Pat::Or(alts) => {
                for alt in alts {
                    if matches!(alt, Pat::Lit(k) if k == key) || matches!(alt, Pat::Wild) {
                        out.push(row[1..].to_vec());
                        break;
                    }
                }
            }
            _ => {}
        }
    }
    out
}

fn default_matrix(matrix: &[Vec<Pat>]) -> Vec<Vec<Pat>> {
    let mut out = Vec::new();
    for row in matrix {
        if row.is_empty() {
            continue;
        }
        match &row[0] {
            Pat::Wild => out.push(row[1..].to_vec()),
            Pat::Or(alts) if alts.iter().any(|a| matches!(a, Pat::Wild)) => {
                out.push(row[1..].to_vec());
            }
            _ => {}
        }
    }
    out
}

fn first_column_heads(matrix: &[Vec<Pat>]) -> Vec<Head> {
    let mut seen = HashSet::new();
    let mut result = Vec::new();
    for row in matrix {
        if let Some(pat) = row.first() {
            collect_heads(pat, &mut seen, &mut result);
        }
    }
    result
}

fn collect_heads(pat: &Pat, seen: &mut HashSet<String>, result: &mut Vec<Head>) {
    match pat {
        Pat::Ctor { name, tag, args } => {
            if seen.insert(format!("ctor_{name}_{tag}")) {
                result.push(Head::Ctor(name.clone(), *tag, args.len()));
            }
        }
        Pat::Lit(k) => {
            if seen.insert(k.to_string_key()) {
                result.push(Head::Lit(k.clone()));
            }
        }
        Pat::Or(alts) => {
            for alt in alts {
                collect_heads(alt, seen, result);
            }
        }
        Pat::Wild => {}
    }
}

fn is_sigma_complete(sigma: &[Head], all_ctors: &HashMap<Name, (u32, usize)>) -> bool {
    if sigma.is_empty() || all_ctors.is_empty() {
        return false;
    }
    let names: HashSet<&Name> = sigma
        .iter()
        .filter_map(|h| match h {
            Head::Ctor(n, _, _) => Some(n),
            _ => None,
        })
        .collect();
    if names.len() == all_ctors.len() && all_ctors.keys().all(|k| names.contains(k)) {
        return true;
    }
    let lits: HashSet<&LitKey> = sigma
        .iter()
        .filter_map(|h| match h {
            Head::Lit(k) => Some(k),
            _ => None,
        })
        .collect();
    lits.len() == 2 && lits.contains(&LitKey::Bool(true)) && lits.contains(&LitKey::Bool(false))
}

fn find_redundant_arms_internal(
    matrix: &[Vec<Pat>],
    all_ctors: &HashMap<Name, (u32, usize)>,
    config: &ExhaustivenessConfig,
) -> Vec<usize> {
    (0..matrix.len())
        .filter(|&i| {
            !useful(
                &matrix[..i],
                &matrix[i],
                all_ctors,
                config.max_pattern_depth,
            )
        })
        .collect()
}

fn desc_to_pat(desc: &PatternDesc) -> Pat {
    match desc {
        PatternDesc::Ctor { name, fields } => Pat::Ctor {
            name: name.clone(),
            tag: 0,
            args: fields.iter().map(desc_to_pat).collect(),
        },
        PatternDesc::Wildcard => Pat::Wild,
        PatternDesc::Literal(lit) => Pat::Lit(LitKey::from_ir(lit)),
        PatternDesc::Or(alts) => Pat::Or(alts.iter().map(desc_to_pat).collect()),
    }
}
