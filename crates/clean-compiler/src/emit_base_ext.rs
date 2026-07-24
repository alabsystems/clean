// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended emission base: output statistics, name collision detection,
//! emission ordering, backend comparison, comment generation, and validation.
//!
//! Extends `emit_base::EmitterBase` with cross-backend analysis utilities
//! that are independent of any particular emission target (C, LLVM, Rust).
//!
//! Part of #3084 - IO/FFI/Native.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use clean_kernel::Name;
use thiserror::Error;

use crate::ir::{IRBody, IRDecl, IRExpr, IRType};
use crate::mangle::mangle_name;

/// Errors from extended emission analysis.
#[derive(Debug, Error)]
pub(crate) enum EmitExtError {
    #[error("name collision: mangled `{mangled}` maps to `{first}` and `{second}`")]
    NameCollision {
        mangled: String,
        first: String,
        second: String,
    },
    #[error("dependency cycle involving `{name}`")]
    DependencyCycle { name: String },
    #[error("undefined reference to `{name}` in `{in_decl}`")]
    UndefinedReference { name: String, in_decl: String },
    #[error("backend mismatch for `{decl}`: {detail}")]
    BackendMismatch { decl: String, detail: String },
}

/// Code generation backend identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Backend {
    C,
    Llvm,
    Rust,
}

impl Backend {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Backend::C => "C",
            Backend::Llvm => "LLVM",
            Backend::Rust => "Rust",
        }
    }
}

/// Per-backend output statistics collected during emission.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct OutputStats {
    pub(crate) lines_of_code: u64,
    pub(crate) declarations_emitted: u64,
    pub(crate) comment_lines: u64,
    pub(crate) blank_lines: u64,
}

impl OutputStats {
    /// Merge stats from another instance (additive).
    pub(crate) fn merge(&mut self, other: &OutputStats) {
        self.lines_of_code += other.lines_of_code;
        self.declarations_emitted += other.declarations_emitted;
        self.comment_lines += other.comment_lines;
        self.blank_lines += other.blank_lines;
    }

    /// Total output lines (code + comments + blanks).
    pub(crate) fn total_lines(&self) -> u64 {
        self.lines_of_code + self.comment_lines + self.blank_lines
    }
}

/// Compute [`OutputStats`] from raw emitted text.
///
/// Classifies lines as blank (whitespace only), comment (`//`, `/*`, `*`
/// prefix), or code.
pub(crate) fn compute_output_stats(text: &str, decl_count: u64) -> OutputStats {
    let mut stats = OutputStats {
        declarations_emitted: decl_count,
        ..Default::default()
    };
    for line in text.lines() {
        let t = line.trim();
        if t.is_empty() {
            stats.blank_lines += 1;
        } else if t.starts_with("//") || t.starts_with("/*") || t.starts_with('*') {
            stats.comment_lines += 1;
        } else {
            stats.lines_of_code += 1;
        }
    }
    stats
}

/// Result of a name collision check.
#[derive(Debug, Clone)]
pub(crate) struct CollisionReport {
    /// Collisions found: mangled name -> set of original names.
    pub(crate) collisions: BTreeMap<String, BTreeSet<String>>,
}

impl CollisionReport {
    pub(crate) fn is_clean(&self) -> bool {
        self.collisions.is_empty()
    }
    pub(crate) fn collision_count(&self) -> usize {
        self.collisions.len()
    }
}

/// Detect name collisions among a set of declarations.
///
/// Two distinct `Name` values that mangle to the same identifier constitute
/// a collision.
pub(crate) fn detect_name_collisions(names: &[Name]) -> CollisionReport {
    let mut seen: HashMap<String, BTreeSet<String>> = HashMap::new();
    for name in names {
        seen.entry(mangle_name(name))
            .or_default()
            .insert(format!("{}", name));
    }
    CollisionReport {
        collisions: seen.into_iter().filter(|(_, v)| v.len() > 1).collect(),
    }
}

/// Compute a valid emission order for declarations respecting call deps.
///
/// Returns indices into `decls` in topological order (callees before callers).
/// Returns `Err` if a dependency cycle is detected.
pub(crate) fn compute_emission_order(decls: &[IRDecl]) -> Result<Vec<usize>, EmitExtError> {
    let name_to_idx: HashMap<String, usize> = decls
        .iter()
        .enumerate()
        .map(|(i, d)| (format!("{}", d.name), i))
        .collect();
    let n = decls.len();
    let mut deps: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    for (i, decl) in decls.iter().enumerate() {
        collect_call_refs_body(&decl.body, &name_to_idx, &mut deps[i]);
    }
    // Kahn's algorithm: in_degree[i] = number of deps i depends on.
    let mut in_deg: Vec<usize> = deps.iter().map(|d| d.len()).collect();
    // Reverse adjacency: for each dep, which nodes depend on it?
    let mut rev: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, d) in deps.iter().enumerate() {
        for &dep in d {
            rev[dep].push(i);
        }
    }
    let mut queue: VecDeque<usize> = (0..n).filter(|&i| in_deg[i] == 0).collect();
    let mut order = Vec::with_capacity(n);
    while let Some(node) = queue.pop_front() {
        order.push(node);
        for &dependent in &rev[node] {
            in_deg[dependent] -= 1;
            if in_deg[dependent] == 0 {
                queue.push_back(dependent);
            }
        }
    }
    if order.len() != n {
        let cycle = (0..n).find(|&i| in_deg[i] > 0).unwrap_or(0);
        return Err(EmitExtError::DependencyCycle {
            name: format!("{}", decls[cycle].name),
        });
    }
    Ok(order)
}

fn collect_call_refs_body(body: &IRBody, idx: &HashMap<String, usize>, out: &mut HashSet<usize>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            collect_call_refs_expr(value, idx, out);
            collect_call_refs_body(rest, idx, out);
        }
        IRBody::JDecl { body: b, rest, .. } => {
            collect_call_refs_body(b, idx, out);
            collect_call_refs_body(rest, idx, out);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => collect_call_refs_body(rest, idx, out),
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_call_refs_body(&alt.body, idx, out);
            }
            if let Some(d) = default {
                collect_call_refs_body(d, idx, out);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn collect_call_refs_expr(expr: &IRExpr, idx: &HashMap<String, usize>, out: &mut HashSet<usize>) {
    if let IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } = expr {
        if let Some(&i) = idx.get(&format!("{}", fn_id.0)) {
            out.insert(i);
        }
    }
}

/// Result of comparing emission output across backends.
#[derive(Debug, Clone)]
pub(crate) struct BackendComparison {
    pub(crate) stats: BTreeMap<Backend, OutputStats>,
    pub(crate) missing_decls: Vec<BackendDeclDiff>,
}

/// A declaration present in some backends but absent in others.
#[derive(Debug, Clone)]
pub(crate) struct BackendDeclDiff {
    pub(crate) decl_name: String,
    pub(crate) present_in: Vec<Backend>,
    pub(crate) absent_from: Vec<Backend>,
}

/// Compare emission results across backends for consistency.
pub(crate) fn compare_backends(
    entries: &[(Backend, BTreeSet<String>, OutputStats)],
) -> BackendComparison {
    let mut stats = BTreeMap::new();
    let mut all_decls: BTreeSet<String> = BTreeSet::new();
    let mut by_backend: BTreeMap<Backend, &BTreeSet<String>> = BTreeMap::new();
    for (b, names, st) in entries {
        stats.insert(*b, st.clone());
        all_decls.extend(names.iter().cloned());
        by_backend.insert(*b, names);
    }
    let missing_decls = all_decls
        .iter()
        .filter_map(|d| {
            let present: Vec<_> = by_backend
                .iter()
                .filter(|(_, n)| n.contains(d))
                .map(|(b, _)| *b)
                .collect();
            let absent: Vec<_> = by_backend
                .iter()
                .filter(|(_, n)| !n.contains(d))
                .map(|(b, _)| *b)
                .collect();
            if absent.is_empty() {
                None
            } else {
                Some(BackendDeclDiff {
                    decl_name: d.clone(),
                    present_in: present,
                    absent_from: absent,
                })
            }
        })
        .collect();
    BackendComparison {
        stats,
        missing_decls,
    }
}

/// Generate a documentation comment from IR declaration metadata.
pub(crate) fn generate_decl_comment(decl: &IRDecl, prefix: &str) -> String {
    let params: Vec<String> = decl
        .params
        .iter()
        .map(|(vid, ty)| format!("_x{}: {}", vid.0, format_ir_type(ty)))
        .collect();
    format!(
        "{} {}({}) -> {}",
        prefix,
        decl.name,
        params.join(", "),
        format_ir_type(&decl.return_type)
    )
}

/// Generate a multi-line module header comment.
pub(crate) fn generate_module_header(module_name: &str, decl_count: usize, prefix: &str) -> String {
    format!(
        "{} Module: {}\n{} Declarations: {}\n{} Generated by clean-compiler\n",
        prefix, module_name, prefix, decl_count, prefix,
    )
}

/// Format an IR type for display in comments.
pub(crate) fn format_ir_type(ty: &IRType) -> String {
    match ty {
        IRType::Bool => "Bool".to_string(),
        IRType::UInt8 => "UInt8".to_string(),
        IRType::UInt16 => "UInt16".to_string(),
        IRType::UInt32 => "UInt32".to_string(),
        IRType::UInt64 => "UInt64".to_string(),
        IRType::USize => "USize".to_string(),
        IRType::Float32 => "Float32".to_string(),
        IRType::Float64 => "Float64".to_string(),
        IRType::Object => "Object".to_string(),
        IRType::TObject => "TObject".to_string(),
        IRType::Struct(f) => format!(
            "Struct({})",
            f.iter().map(format_ir_type).collect::<Vec<_>>().join(", ")
        ),
        IRType::Union(v) => format!(
            "Union({})",
            v.iter().map(format_ir_type).collect::<Vec<_>>().join(", ")
        ),
        IRType::Erased => "Erased".to_string(),
        IRType::Void => "Void".to_string(),
    }
}

/// Validation issue found in emitted output.
#[derive(Debug, Clone)]
pub(crate) struct ValidationIssue {
    pub(crate) severity: IssueSeverity,
    pub(crate) message: String,
    pub(crate) decl_name: Option<String>,
}

/// Severity of a validation issue.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum IssueSeverity {
    Info,
    Warning,
    Error,
}

/// Validate IR declarations for common emission problems.
///
/// Checks: duplicate names, undefined function references, unreachable
/// bodies, void-typed parameters.
pub(crate) fn validate_declarations(decls: &[IRDecl]) -> Vec<ValidationIssue> {
    let mut issues = Vec::new();
    let known: HashSet<String> = decls.iter().map(|d| format!("{}", d.name)).collect();
    let mut seen: HashSet<String> = HashSet::new();
    for decl in decls {
        let name = format!("{}", decl.name);
        if !seen.insert(name.clone()) {
            issues.push(ValidationIssue {
                severity: IssueSeverity::Error,
                message: format!("duplicate declaration name: `{}`", name),
                decl_name: Some(name.clone()),
            });
        }
    }
    for decl in decls {
        let dn = format!("{}", decl.name);
        let mut refs = HashSet::new();
        collect_call_names_body(&decl.body, &mut refs);
        for r in &refs {
            if !known.contains(r) {
                issues.push(ValidationIssue {
                    severity: IssueSeverity::Warning,
                    message: format!("undefined reference to `{}` in `{}`", r, dn),
                    decl_name: Some(dn.clone()),
                });
            }
        }
        if matches!(decl.body, IRBody::Unreachable) {
            issues.push(ValidationIssue {
                severity: IssueSeverity::Info,
                message: format!("`{}` has unreachable body", dn),
                decl_name: Some(dn.clone()),
            });
        }
        for (vid, ty) in &decl.params {
            if ty.is_void() {
                issues.push(ValidationIssue {
                    severity: IssueSeverity::Warning,
                    message: format!("_x{} in `{}` has Void type (erasure bug?)", vid.0, dn),
                    decl_name: Some(dn.clone()),
                });
            }
        }
    }
    issues
}

fn collect_call_names_body(body: &IRBody, out: &mut HashSet<String>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            collect_call_names_expr(value, out);
            collect_call_names_body(rest, out);
        }
        IRBody::JDecl { body: b, rest, .. } => {
            collect_call_names_body(b, out);
            collect_call_names_body(rest, out);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => collect_call_names_body(rest, out),
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_call_names_body(&alt.body, out);
            }
            if let Some(d) = default {
                collect_call_names_body(d, out);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn collect_call_names_expr(expr: &IRExpr, out: &mut HashSet<String>) {
    if let IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } = expr {
        out.insert(format!("{}", fn_id.0));
    }
}

/// Target architecture hint for emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum EmitTarget {
    X86_64,
    AArch64,
    Wasm32,
    Generic,
}

/// Optimization level for emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum OptLevel {
    O0,
    O1,
    O2,
    O3,
}

/// Configurable emission options that apply across all backends.
#[derive(Debug, Clone)]
pub(crate) struct EmitConfig {
    pub(crate) debug_info: bool,
    pub(crate) opt_level: OptLevel,
    pub(crate) target: EmitTarget,
    pub(crate) module_header: bool,
    pub(crate) decl_comments: bool,
}

impl Default for EmitConfig {
    fn default() -> Self {
        Self {
            debug_info: false,
            opt_level: OptLevel::O0,
            target: EmitTarget::Generic,
            module_header: true,
            decl_comments: false,
        }
    }
}

impl EmitConfig {
    pub(crate) fn debug() -> Self {
        Self {
            debug_info: true,
            decl_comments: true,
            ..Default::default()
        }
    }
    pub(crate) fn release() -> Self {
        Self {
            opt_level: OptLevel::O2,
            ..Default::default()
        }
    }
}
