// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hash-consing decompression for proof certificates.
//!
//! Reconstructs original certificate structures from their
//! deduplicated compressed form.

use crate::expr::{stack_safe, BigNat, Expr, ExprKind, LevelVec, Literal, MDataMap};
use crate::level::Level;

use std::mem::size_of;
use std::sync::Arc;

use super::super::{DefEqStep, ProofCert, ZFCSetCertKind};
use super::limits::{
    MAX_COMPRESSED_TABLE_ENTRIES, MAX_DECOMPRESSED_CERT_BYTES, MAX_DECOMPRESSED_CERT_NODES,
};
use super::types::{
    CertIdx, CompressedCert, CompressedCertNode, CompressedExpr, CompressedLevel, ExprIdx, LevelIdx,
};

/// Error during certificate decompression
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum DecompressError {
    /// Invalid expression index
    #[error("Invalid expression index: {0}")]
    InvalidExprIndex(ExprIdx),
    /// Invalid level index
    #[error("Invalid level index: {0}")]
    InvalidLevelIndex(LevelIdx),
    /// Invalid certificate index
    #[error("Invalid certificate index: {0}")]
    InvalidCertIndex(CertIdx),
    /// The in-memory raw compressed-certificate schema is not current.
    #[error("invalid raw compressed-certificate schema")]
    InvalidSchema,
    /// A compressed table exceeds its resource limit.
    #[error("{table} table has {count} entries, exceeding maximum {max}")]
    TableLimit {
        /// Table name.
        table: &'static str,
        /// Actual entry count.
        count: usize,
        /// Maximum accepted entry count.
        max: usize,
    },
    /// A same-table edge is not in canonical child-before-parent order.
    #[error(
        "non-canonical {table} reference: parent index {parent} references child index {child}"
    )]
    NonCanonicalReference {
        /// Table name.
        table: &'static str,
        /// Parent index.
        parent: u32,
        /// Referenced child index.
        child: u32,
    },
    /// Expanding a shared certificate DAG would exceed the output budget.
    #[error("expanded certificate has at least {nodes} nodes, exceeding maximum {max}")]
    ExpandedCertLimit {
        /// Expanded node count, saturated at one past the limit.
        nodes: usize,
        /// Maximum reconstructed certificate/definitional-equality nodes.
        max: usize,
    },
    /// Expanded owned payload would exceed the output byte budget.
    #[error("expanded certificate requires at least {bytes} bytes, exceeding maximum {max}")]
    ExpandedCertByteLimit {
        /// Estimated owned bytes, saturated at one past the limit.
        bytes: usize,
        /// Maximum reconstructed owned bytes.
        max: usize,
    },
}

/// State for certificate decompression
pub(crate) struct DecompressionState<'a> {
    compressed: &'a CompressedCert,
    level_cache: Vec<Option<Level>>,
    expr_cache: Vec<Option<Expr>>,
}

impl<'a> DecompressionState<'a> {
    pub(crate) fn new(compressed: &'a CompressedCert) -> Self {
        Self {
            compressed,
            // Indices are dense and validated child-before-parent before this
            // state is constructed.  Vec slots have exact, preflighted memory
            // cost and avoid attacker-shaped HashMap buckets and rehashing.
            level_cache: vec![None; compressed.levels.len()],
            expr_cache: vec![None; compressed.exprs.len()],
        }
    }

    /// Decompress a level by index.
    pub(crate) fn decompress_level(&mut self, idx: LevelIdx) -> Result<Level, DecompressError> {
        stack_safe(|| self.decompress_level_impl(idx))
    }

    fn decompress_level_impl(&mut self, idx: LevelIdx) -> Result<Level, DecompressError> {
        if let Some(Some(level)) = self.level_cache.get(idx as usize) {
            return Ok(level.clone());
        }

        let compressed = self
            .compressed
            .levels
            .get(idx as usize)
            .ok_or(DecompressError::InvalidLevelIndex(idx))?;

        let level = match compressed {
            CompressedLevel::Zero => Level::Zero,
            CompressedLevel::Succ(l_idx) => {
                Level::Succ(crate::level::level_arc(self.decompress_level(*l_idx)?))
            }
            CompressedLevel::Max(l1_idx, l2_idx) => {
                let l1 = self.decompress_level(*l1_idx)?;
                let l2 = self.decompress_level(*l2_idx)?;
                Level::Max(crate::level::level_arc(l1), crate::level::level_arc(l2))
            }
            CompressedLevel::IMax(l1_idx, l2_idx) => {
                let l1 = self.decompress_level(*l1_idx)?;
                let l2 = self.decompress_level(*l2_idx)?;
                Level::IMax(crate::level::level_arc(l1), crate::level::level_arc(l2))
            }
            CompressedLevel::Param(n) => Level::Param(n.clone()),
        };

        self.level_cache[idx as usize] = Some(level.clone());
        Ok(level)
    }

    /// Decompress an expression by index.
    pub(crate) fn decompress_expr(&mut self, idx: ExprIdx) -> Result<Expr, DecompressError> {
        stack_safe(|| self.decompress_expr_impl(idx))
    }

    fn decompress_expr_impl(&mut self, idx: ExprIdx) -> Result<Expr, DecompressError> {
        if let Some(Some(expr)) = self.expr_cache.get(idx as usize) {
            return Ok(expr.clone());
        }

        let compressed = self
            .compressed
            .exprs
            .get(idx as usize)
            .ok_or(DecompressError::InvalidExprIndex(idx))?
            .clone();

        let expr = match compressed {
            CompressedExpr::BVar(i) => Expr::from_kind(ExprKind::BVar(i)),
            CompressedExpr::FVar(id) => Expr::from_kind(ExprKind::FVar(id)),
            CompressedExpr::Sort(l_idx) => {
                Expr::from_kind(ExprKind::Sort(self.decompress_level(l_idx)?))
            }
            CompressedExpr::Const(n, level_idxs) => {
                let levels: Result<LevelVec, _> = level_idxs
                    .iter()
                    .map(|&idx| self.decompress_level(idx))
                    .collect();
                Expr::from_kind(ExprKind::Const(n, levels?))
            }
            CompressedExpr::App(f_idx, a_idx) => {
                let f = self.decompress_expr(f_idx)?;
                let a = self.decompress_expr(a_idx)?;
                Expr::from_kind(ExprKind::App(f.into(), a.into()))
            }
            CompressedExpr::Lam(binder, ty_idx, body_idx) => {
                let ty = self.decompress_expr(ty_idx)?;
                let body = self.decompress_expr(body_idx)?;
                Expr::from_kind(ExprKind::Lam(binder, ty.into(), body.into()))
            }
            CompressedExpr::Pi(binder, ty_idx, body_idx) => {
                let ty = self.decompress_expr(ty_idx)?;
                let body = self.decompress_expr(body_idx)?;
                Expr::from_kind(ExprKind::Pi(binder, ty.into(), body.into()))
            }
            CompressedExpr::Let(name, ty_idx, val_idx, body_idx, non_dep) => {
                let ty = self.decompress_expr(ty_idx)?;
                let val = self.decompress_expr(val_idx)?;
                let body = self.decompress_expr(body_idx)?;
                Expr::from_kind(ExprKind::Let(
                    name,
                    ty.into(),
                    val.into(),
                    body.into(),
                    non_dep,
                ))
            }
            CompressedExpr::Lit(lit) => Expr::from_kind(ExprKind::Lit(lit)),
            CompressedExpr::Proj(n, i, e_idx) => {
                let e = self.decompress_expr(e_idx)?;
                Expr::from_kind(ExprKind::Proj(n, i, Arc::new(e)))
            }
            CompressedExpr::MData(md, e_idx) => {
                let e = self.decompress_expr(e_idx)?;
                Expr::from_kind(ExprKind::MData(md, e.into()))
            }
        };

        self.expr_cache[idx as usize] = Some(expr.clone());
        Ok(expr)
    }

    /// Decompress a certificate by index.
    pub(crate) fn decompress_cert(&mut self, idx: CertIdx) -> Result<ProofCert, DecompressError> {
        stack_safe(|| self.decompress_cert_impl(idx))
    }

    fn decompress_cert_impl(&mut self, idx: CertIdx) -> Result<ProofCert, DecompressError> {
        let compressed = self.compressed;
        let node = compressed
            .certs
            .get(idx as usize)
            .ok_or(DecompressError::InvalidCertIndex(idx))?;

        self.decompress_cert_node(node)
    }

    /// Decompress core certificate node variants (Sort through Lam).
    fn decompress_cert_node(
        &mut self,
        node: &CompressedCertNode,
    ) -> Result<ProofCert, DecompressError> {
        match node {
            CompressedCertNode::Sort { level } => Ok(ProofCert::Sort {
                level: self.decompress_level(*level)?,
            }),
            CompressedCertNode::BVar { idx, expected_type } => Ok(ProofCert::BVar {
                idx: *idx,
                expected_type: Box::new(self.decompress_expr(*expected_type)?),
            }),
            CompressedCertNode::FVar { id, type_ } => Ok(ProofCert::FVar {
                id: *id,
                type_: Box::new(self.decompress_expr(*type_)?),
            }),
            CompressedCertNode::Const {
                name,
                levels,
                type_,
            } => {
                let lvls: Result<Vec<_>, _> = levels
                    .iter()
                    .map(|&idx| self.decompress_level(idx))
                    .collect();
                Ok(ProofCert::Const {
                    name: name.clone(),
                    levels: lvls?,
                    type_: Box::new(self.decompress_expr(*type_)?),
                })
            }
            CompressedCertNode::App {
                fn_cert,
                fn_type,
                arg_cert,
                result_type,
            } => Ok(ProofCert::App {
                fn_cert: Box::new(self.decompress_cert(*fn_cert)?),
                fn_type: Box::new(self.decompress_expr(*fn_type)?),
                arg_cert: Box::new(self.decompress_cert(*arg_cert)?),
                result_type: Box::new(self.decompress_expr(*result_type)?),
            }),
            CompressedCertNode::Lam {
                binder_info,
                arg_type_cert,
                body_cert,
                result_type,
            } => Ok(ProofCert::Lam {
                binder_info: *binder_info,
                arg_type_cert: Box::new(self.decompress_cert(*arg_type_cert)?),
                body_cert: Box::new(self.decompress_cert(*body_cert)?),
                result_type: Box::new(self.decompress_expr(*result_type)?),
            }),
            _ => self.decompress_cert_compound(node),
        }
    }

    /// Decompress compound certificate variants (Pi through ModeSpecific).
    fn decompress_cert_compound(
        &mut self,
        node: &CompressedCertNode,
    ) -> Result<ProofCert, DecompressError> {
        match node {
            CompressedCertNode::Pi {
                binder_info,
                arg_type_cert,
                arg_level,
                body_type_cert,
                body_level,
            } => Ok(ProofCert::Pi {
                binder_info: *binder_info,
                arg_type_cert: Box::new(self.decompress_cert(*arg_type_cert)?),
                arg_level: self.decompress_level(*arg_level)?,
                body_type_cert: Box::new(self.decompress_cert(*body_type_cert)?),
                body_level: self.decompress_level(*body_level)?,
            }),
            CompressedCertNode::Let {
                type_cert,
                value_cert,
                body_cert,
                result_type,
            } => Ok(ProofCert::Let {
                type_cert: Box::new(self.decompress_cert(*type_cert)?),
                value_cert: Box::new(self.decompress_cert(*value_cert)?),
                body_cert: Box::new(self.decompress_cert(*body_cert)?),
                result_type: Box::new(self.decompress_expr(*result_type)?),
            }),
            CompressedCertNode::Lit { lit, type_ } => Ok(ProofCert::Lit {
                lit: lit.clone(),
                type_: Box::new(self.decompress_expr(*type_)?),
            }),
            CompressedCertNode::DefEq {
                inner,
                expected_type,
                actual_type,
                eq_steps,
            } => Ok(ProofCert::DefEq {
                inner: Box::new(self.decompress_cert(*inner)?),
                expected_type: Box::new(self.decompress_expr(*expected_type)?),
                actual_type: Box::new(self.decompress_expr(*actual_type)?),
                eq_steps: eq_steps.clone(),
            }),
            CompressedCertNode::MData {
                metadata,
                inner_cert,
                result_type,
            } => Ok(ProofCert::MData {
                metadata: metadata.clone(),
                inner_cert: Box::new(self.decompress_cert(*inner_cert)?),
                result_type: Box::new(self.decompress_expr(*result_type)?),
            }),
            CompressedCertNode::Proj {
                struct_name,
                idx,
                expr_cert,
                expr_type,
                field_type,
            } => Ok(ProofCert::Proj {
                struct_name: struct_name.clone(),
                idx: *idx,
                expr_cert: Box::new(self.decompress_cert(*expr_cert)?),
                expr_type: Box::new(self.decompress_expr(*expr_type)?),
                field_type: Box::new(self.decompress_expr(*field_type)?),
            }),
            CompressedCertNode::ModeSpecific(cert) => Ok(*cert.clone()),
            _ => unreachable!("all variants handled by decompress_cert_node"),
        }
    }
}

fn validate_compressed(compressed: &CompressedCert) -> Result<(), DecompressError> {
    if !compressed.schema.is_current() {
        return Err(DecompressError::InvalidSchema);
    }
    for (table, count) in [
        ("level", compressed.levels.len()),
        ("expression", compressed.exprs.len()),
        ("certificate", compressed.certs.len()),
    ] {
        if count > MAX_COMPRESSED_TABLE_ENTRIES {
            return Err(DecompressError::TableLimit {
                table,
                count,
                max: MAX_COMPRESSED_TABLE_ENTRIES,
            });
        }
    }

    for (parent, level) in compressed.levels.iter().enumerate() {
        let parent = parent as u32;
        match level {
            CompressedLevel::Zero | CompressedLevel::Param(_) => {}
            CompressedLevel::Succ(child) => {
                validate_prior_level(compressed, parent, *child)?;
            }
            CompressedLevel::Max(left, right) | CompressedLevel::IMax(left, right) => {
                validate_prior_level(compressed, parent, *left)?;
                validate_prior_level(compressed, parent, *right)?;
            }
        }
    }

    for (parent, expr) in compressed.exprs.iter().enumerate() {
        let parent = parent as u32;
        match expr {
            CompressedExpr::BVar(_) | CompressedExpr::FVar(_) | CompressedExpr::Lit(_) => {}
            CompressedExpr::Sort(level) => validate_level_index(compressed, *level)?,
            CompressedExpr::Const(_, levels) => {
                for level in levels {
                    validate_level_index(compressed, *level)?;
                }
            }
            CompressedExpr::App(func, arg)
            | CompressedExpr::Lam(_, func, arg)
            | CompressedExpr::Pi(_, func, arg) => {
                validate_prior_expr(compressed, parent, *func)?;
                validate_prior_expr(compressed, parent, *arg)?;
            }
            CompressedExpr::Let(_, ty, value, body, _) => {
                validate_prior_expr(compressed, parent, *ty)?;
                validate_prior_expr(compressed, parent, *value)?;
                validate_prior_expr(compressed, parent, *body)?;
            }
            CompressedExpr::Proj(_, _, expr) | CompressedExpr::MData(_, expr) => {
                validate_prior_expr(compressed, parent, *expr)?;
            }
        }
    }

    for (parent, cert) in compressed.certs.iter().enumerate() {
        let parent = parent as u32;
        match cert {
            CompressedCertNode::Sort { level } => validate_level_index(compressed, *level)?,
            CompressedCertNode::BVar { expected_type, .. }
            | CompressedCertNode::FVar {
                type_: expected_type,
                ..
            }
            | CompressedCertNode::Lit {
                type_: expected_type,
                ..
            } => validate_expr_index(compressed, *expected_type)?,
            CompressedCertNode::Const { levels, type_, .. } => {
                for level in levels {
                    validate_level_index(compressed, *level)?;
                }
                validate_expr_index(compressed, *type_)?;
            }
            CompressedCertNode::App {
                fn_cert,
                fn_type,
                arg_cert,
                result_type,
            } => {
                validate_prior_cert(compressed, parent, *fn_cert)?;
                validate_expr_index(compressed, *fn_type)?;
                validate_prior_cert(compressed, parent, *arg_cert)?;
                validate_expr_index(compressed, *result_type)?;
            }
            CompressedCertNode::Lam {
                arg_type_cert,
                body_cert,
                result_type,
                ..
            } => {
                validate_prior_cert(compressed, parent, *arg_type_cert)?;
                validate_prior_cert(compressed, parent, *body_cert)?;
                validate_expr_index(compressed, *result_type)?;
            }
            CompressedCertNode::Pi {
                arg_type_cert,
                arg_level,
                body_type_cert,
                body_level,
                ..
            } => {
                validate_prior_cert(compressed, parent, *arg_type_cert)?;
                validate_level_index(compressed, *arg_level)?;
                validate_prior_cert(compressed, parent, *body_type_cert)?;
                validate_level_index(compressed, *body_level)?;
            }
            CompressedCertNode::Let {
                type_cert,
                value_cert,
                body_cert,
                result_type,
            } => {
                validate_prior_cert(compressed, parent, *type_cert)?;
                validate_prior_cert(compressed, parent, *value_cert)?;
                validate_prior_cert(compressed, parent, *body_cert)?;
                validate_expr_index(compressed, *result_type)?;
            }
            CompressedCertNode::DefEq {
                inner,
                expected_type,
                actual_type,
                ..
            } => {
                validate_prior_cert(compressed, parent, *inner)?;
                validate_expr_index(compressed, *expected_type)?;
                validate_expr_index(compressed, *actual_type)?;
            }
            CompressedCertNode::MData {
                inner_cert,
                result_type,
                ..
            } => {
                validate_prior_cert(compressed, parent, *inner_cert)?;
                validate_expr_index(compressed, *result_type)?;
            }
            CompressedCertNode::Proj {
                expr_cert,
                expr_type,
                field_type,
                ..
            } => {
                validate_prior_cert(compressed, parent, *expr_cert)?;
                validate_expr_index(compressed, *expr_type)?;
                validate_expr_index(compressed, *field_type)?;
            }
            CompressedCertNode::ModeSpecific(_) => {}
        }
    }

    validate_cert_index(compressed, compressed.root)?;
    validate_expanded_cert_cost(compressed)
}

fn validate_expanded_cert_cost(compressed: &CompressedCert) -> Result<(), DecompressError> {
    // Same-table references were already proven child-before-parent, so this
    // is a bottom-up dynamic program.  It computes the size of the *owned*
    // ProofCert tree that reconstruction would produce, not merely the number
    // of compressed DAG nodes.
    let expr_clone_costs: Vec<usize> = compressed
        .exprs
        .iter()
        .map(compressed_expr_local_owned_bytes)
        .collect();
    let reachable = reachable_tables(compressed);

    let mut costs: Vec<ExpandedCost> = Vec::with_capacity(compressed.certs.len());
    for node in &compressed.certs {
        let mut cost = ExpandedCost {
            nodes: 1,
            bytes: compressed_node_local_bytes(node, &expr_clone_costs)?,
        };
        match node {
            CompressedCertNode::App {
                fn_cert, arg_cert, ..
            }
            | CompressedCertNode::Lam {
                arg_type_cert: fn_cert,
                body_cert: arg_cert,
                ..
            }
            | CompressedCertNode::Pi {
                arg_type_cert: fn_cert,
                body_type_cert: arg_cert,
                ..
            } => {
                add_child_cost(&mut cost, costs[*fn_cert as usize])?;
                add_child_cost(&mut cost, costs[*arg_cert as usize])?;
            }
            CompressedCertNode::Let {
                type_cert,
                value_cert,
                body_cert,
                ..
            } => {
                add_child_cost(&mut cost, costs[*type_cert as usize])?;
                add_child_cost(&mut cost, costs[*value_cert as usize])?;
                add_child_cost(&mut cost, costs[*body_cert as usize])?;
            }
            CompressedCertNode::DefEq {
                inner, eq_steps, ..
            } => {
                add_child_cost(&mut cost, costs[*inner as usize])?;
                for step in eq_steps {
                    add_def_eq_step_cost(step, &mut cost)?;
                }
            }
            CompressedCertNode::MData { inner_cert, .. } => {
                add_child_cost(&mut cost, costs[*inner_cert as usize])?;
            }
            CompressedCertNode::Proj { expr_cert, .. } => {
                add_child_cost(&mut cost, costs[*expr_cert as usize])?;
            }
            CompressedCertNode::ModeSpecific(cert) => {
                add_embedded_cert_cost(cert, &mut cost)?;
            }
            CompressedCertNode::Sort { .. }
            | CompressedCertNode::BVar { .. }
            | CompressedCertNode::FVar { .. }
            | CompressedCertNode::Const { .. }
            | CompressedCertNode::Lit { .. } => {}
        }
        costs.push(cost);
    }
    let root = &mut costs[compressed.root as usize];
    add_table_construction_cost(compressed, &reachable, &expr_clone_costs, root)?;
    Ok(())
}

struct ReachableTables {
    exprs: Vec<bool>,
    levels: Vec<bool>,
}

fn reachable_tables(compressed: &CompressedCert) -> ReachableTables {
    let mut cert_seen = vec![false; compressed.certs.len()];
    let mut exprs = vec![false; compressed.exprs.len()];
    let mut levels = vec![false; compressed.levels.len()];
    let mut cert_pending = vec![compressed.root];
    let mut expr_pending = Vec::new();
    let mut level_pending = Vec::new();

    while let Some(index) = cert_pending.pop() {
        let slot = &mut cert_seen[index as usize];
        if *slot {
            continue;
        }
        *slot = true;
        match &compressed.certs[index as usize] {
            CompressedCertNode::Sort { level } => level_pending.push(*level),
            CompressedCertNode::BVar { expected_type, .. }
            | CompressedCertNode::FVar {
                type_: expected_type,
                ..
            }
            | CompressedCertNode::Lit {
                type_: expected_type,
                ..
            } => expr_pending.push(*expected_type),
            CompressedCertNode::Const { levels, type_, .. } => {
                level_pending.extend(levels.iter().copied());
                expr_pending.push(*type_);
            }
            CompressedCertNode::App {
                fn_cert,
                fn_type,
                arg_cert,
                result_type,
            } => {
                cert_pending.extend([*fn_cert, *arg_cert]);
                expr_pending.extend([*fn_type, *result_type]);
            }
            CompressedCertNode::Lam {
                arg_type_cert,
                body_cert,
                result_type,
                ..
            } => {
                cert_pending.extend([*arg_type_cert, *body_cert]);
                expr_pending.push(*result_type);
            }
            CompressedCertNode::Pi {
                arg_type_cert,
                arg_level,
                body_type_cert,
                body_level,
                ..
            } => {
                cert_pending.extend([*arg_type_cert, *body_type_cert]);
                level_pending.extend([*arg_level, *body_level]);
            }
            CompressedCertNode::Let {
                type_cert,
                value_cert,
                body_cert,
                result_type,
            } => {
                cert_pending.extend([*type_cert, *value_cert, *body_cert]);
                expr_pending.push(*result_type);
            }
            CompressedCertNode::DefEq {
                inner,
                expected_type,
                actual_type,
                ..
            } => {
                cert_pending.push(*inner);
                expr_pending.extend([*expected_type, *actual_type]);
            }
            CompressedCertNode::MData {
                inner_cert,
                result_type,
                ..
            } => {
                cert_pending.push(*inner_cert);
                expr_pending.push(*result_type);
            }
            CompressedCertNode::Proj {
                expr_cert,
                expr_type,
                field_type,
                ..
            } => {
                cert_pending.push(*expr_cert);
                expr_pending.extend([*expr_type, *field_type]);
            }
            CompressedCertNode::ModeSpecific(_) => {}
        }
    }

    while let Some(index) = expr_pending.pop() {
        let slot = &mut exprs[index as usize];
        if *slot {
            continue;
        }
        *slot = true;
        match &compressed.exprs[index as usize] {
            CompressedExpr::BVar(_) | CompressedExpr::FVar(_) | CompressedExpr::Lit(_) => {}
            CompressedExpr::Sort(level) => level_pending.push(*level),
            CompressedExpr::Const(_, referenced_levels) => {
                level_pending.extend(referenced_levels.iter().copied());
            }
            CompressedExpr::App(left, right)
            | CompressedExpr::Lam(_, left, right)
            | CompressedExpr::Pi(_, left, right) => {
                expr_pending.extend([*left, *right]);
            }
            CompressedExpr::Let(_, ty, value, body, _) => {
                expr_pending.extend([*ty, *value, *body]);
            }
            CompressedExpr::Proj(_, _, inner) | CompressedExpr::MData(_, inner) => {
                expr_pending.push(*inner);
            }
        }
    }

    while let Some(index) = level_pending.pop() {
        let slot = &mut levels[index as usize];
        if *slot {
            continue;
        }
        *slot = true;
        match &compressed.levels[index as usize] {
            CompressedLevel::Zero | CompressedLevel::Param(_) => {}
            CompressedLevel::Succ(child) => level_pending.push(*child),
            CompressedLevel::Max(left, right) | CompressedLevel::IMax(left, right) => {
                level_pending.extend([*left, *right]);
            }
        }
    }

    ReachableTables { exprs, levels }
}

fn add_table_construction_cost(
    compressed: &CompressedCert,
    reachable: &ReachableTables,
    expr_clone_costs: &[usize],
    total: &mut ExpandedCost,
) -> Result<(), DecompressError> {
    // Dense Vec<Option<T>> cache slots are allocated for the full validated
    // tables.  Charge those exact allocations before constructing the state.
    add_sized_payload(
        &mut total.bytes,
        compressed.exprs.len(),
        size_of::<Option<Expr>>(),
    )?;
    add_sized_payload(
        &mut total.bytes,
        compressed.levels.len(),
        size_of::<Option<Level>>(),
    )?;

    for (index, expr) in compressed.exprs.iter().enumerate() {
        if !reachable.exprs[index] {
            continue;
        }
        add_expanded_nodes(&mut total.nodes, 1)?;
        // The cache slot contains the Expr inline; only its root-owned dynamic
        // payload is additional.
        add_expanded_bytes(&mut total.bytes, expr_clone_costs[index])?;
        match expr {
            CompressedExpr::App(left, right)
            | CompressedExpr::Lam(_, left, right)
            | CompressedExpr::Pi(_, left, right) => {
                add_arc_expr_clone_bytes(&mut total.bytes, *left, expr_clone_costs)?;
                add_arc_expr_clone_bytes(&mut total.bytes, *right, expr_clone_costs)?;
            }
            CompressedExpr::Let(_, ty, value, body, _) => {
                add_arc_expr_clone_bytes(&mut total.bytes, *ty, expr_clone_costs)?;
                add_arc_expr_clone_bytes(&mut total.bytes, *value, expr_clone_costs)?;
                add_arc_expr_clone_bytes(&mut total.bytes, *body, expr_clone_costs)?;
            }
            CompressedExpr::Proj(_, _, inner) | CompressedExpr::MData(_, inner) => {
                add_arc_expr_clone_bytes(&mut total.bytes, *inner, expr_clone_costs)?;
            }
            CompressedExpr::BVar(_)
            | CompressedExpr::FVar(_)
            | CompressedExpr::Sort(_)
            | CompressedExpr::Const(_, _)
            | CompressedExpr::Lit(_) => {}
        }
    }

    for (index, level) in compressed.levels.iter().enumerate() {
        if !reachable.levels[index] {
            continue;
        }
        add_expanded_nodes(&mut total.nodes, 1)?;
        let edge_count = match level {
            CompressedLevel::Zero | CompressedLevel::Param(_) => 0,
            CompressedLevel::Succ(_) => 1,
            CompressedLevel::Max(_, _) | CompressedLevel::IMax(_, _) => 2,
        };
        add_sized_payload(
            &mut total.bytes,
            edge_count,
            size_of::<Level>() + 2 * size_of::<usize>(),
        )?;
    }
    Ok(())
}

fn add_arc_expr_clone_bytes(
    bytes: &mut usize,
    child: ExprIdx,
    expr_clone_costs: &[usize],
) -> Result<(), DecompressError> {
    add_expanded_bytes(bytes, size_of::<Expr>() + 2 * size_of::<usize>())?;
    add_expanded_bytes(bytes, expr_clone_costs[child as usize])
}

#[derive(Clone, Copy)]
struct ExpandedCost {
    nodes: usize,
    bytes: usize,
}

fn add_child_cost(total: &mut ExpandedCost, child: ExpandedCost) -> Result<(), DecompressError> {
    add_expanded_nodes(&mut total.nodes, child.nodes)?;
    add_expanded_bytes(&mut total.bytes, child.bytes)
}

fn add_expanded_nodes(total: &mut usize, additional: usize) -> Result<(), DecompressError> {
    let next = total
        .checked_add(additional)
        .unwrap_or(MAX_DECOMPRESSED_CERT_NODES.saturating_add(1));
    if next > MAX_DECOMPRESSED_CERT_NODES {
        return Err(DecompressError::ExpandedCertLimit {
            nodes: next.min(MAX_DECOMPRESSED_CERT_NODES.saturating_add(1)),
            max: MAX_DECOMPRESSED_CERT_NODES,
        });
    }
    *total = next;
    Ok(())
}

fn add_expanded_bytes(total: &mut usize, additional: usize) -> Result<(), DecompressError> {
    let next = total
        .checked_add(additional)
        .unwrap_or(MAX_DECOMPRESSED_CERT_BYTES.saturating_add(1));
    if next > MAX_DECOMPRESSED_CERT_BYTES {
        return Err(DecompressError::ExpandedCertByteLimit {
            bytes: next.min(MAX_DECOMPRESSED_CERT_BYTES.saturating_add(1)),
            max: MAX_DECOMPRESSED_CERT_BYTES,
        });
    }
    *total = next;
    Ok(())
}

fn add_sized_payload(
    total: &mut usize,
    count: usize,
    element_size: usize,
) -> Result<(), DecompressError> {
    let bytes = count
        .checked_mul(element_size)
        .unwrap_or(MAX_DECOMPRESSED_CERT_BYTES.saturating_add(1));
    add_expanded_bytes(total, bytes)
}

fn literal_owned_bytes(literal: &Literal) -> usize {
    match literal {
        Literal::Nat(BigNat::Small(_)) | Literal::String(_) => 0,
        Literal::Nat(BigNat::Big(limbs)) => limbs.len().saturating_mul(size_of::<u64>()),
    }
}

fn compressed_expr_local_owned_bytes(expr: &CompressedExpr) -> usize {
    match expr {
        CompressedExpr::Const(_, levels) => levels.len().saturating_mul(size_of::<Level>()),
        CompressedExpr::Lit(literal) => literal_owned_bytes(literal),
        CompressedExpr::MData(metadata, _) => metadata
            .len()
            .saturating_mul(size_of::<<MDataMap as IntoIterator>::Item>()),
        CompressedExpr::BVar(_)
        | CompressedExpr::FVar(_)
        | CompressedExpr::Sort(_)
        | CompressedExpr::App(_, _)
        | CompressedExpr::Lam(_, _, _)
        | CompressedExpr::Pi(_, _, _)
        | CompressedExpr::Let(_, _, _, _, _)
        | CompressedExpr::Proj(_, _, _) => 0,
    }
}

fn add_expr_reference_bytes(
    bytes: &mut usize,
    expr_idx: ExprIdx,
    expr_clone_costs: &[usize],
) -> Result<(), DecompressError> {
    add_expanded_bytes(bytes, size_of::<Expr>())?;
    add_expanded_bytes(bytes, expr_clone_costs[expr_idx as usize])
}

fn compressed_node_local_bytes(
    node: &CompressedCertNode,
    expr_clone_costs: &[usize],
) -> Result<usize, DecompressError> {
    let mut bytes = size_of::<ProofCert>();
    match node {
        CompressedCertNode::Sort { .. } | CompressedCertNode::Pi { .. } => {}
        CompressedCertNode::BVar { expected_type, .. } => {
            add_expr_reference_bytes(&mut bytes, *expected_type, expr_clone_costs)?;
        }
        CompressedCertNode::FVar { type_, .. } | CompressedCertNode::Lit { type_, .. } => {
            add_expr_reference_bytes(&mut bytes, *type_, expr_clone_costs)?;
        }
        CompressedCertNode::Lam { result_type, .. }
        | CompressedCertNode::Let { result_type, .. }
        | CompressedCertNode::MData { result_type, .. } => {
            add_expr_reference_bytes(&mut bytes, *result_type, expr_clone_costs)?;
        }
        CompressedCertNode::Const { levels, type_, .. } => {
            add_expr_reference_bytes(&mut bytes, *type_, expr_clone_costs)?;
            add_sized_payload(&mut bytes, levels.len(), size_of::<Level>())?;
        }
        CompressedCertNode::App {
            fn_type,
            result_type,
            ..
        } => {
            add_expr_reference_bytes(&mut bytes, *fn_type, expr_clone_costs)?;
            add_expr_reference_bytes(&mut bytes, *result_type, expr_clone_costs)?;
        }
        CompressedCertNode::DefEq {
            expected_type,
            actual_type,
            ..
        } => {
            add_expr_reference_bytes(&mut bytes, *expected_type, expr_clone_costs)?;
            add_expr_reference_bytes(&mut bytes, *actual_type, expr_clone_costs)?;
        }
        CompressedCertNode::Proj {
            expr_type,
            field_type,
            ..
        } => {
            add_expr_reference_bytes(&mut bytes, *expr_type, expr_clone_costs)?;
            add_expr_reference_bytes(&mut bytes, *field_type, expr_clone_costs)?;
        }
        CompressedCertNode::ModeSpecific(_) => {}
    }
    match node {
        CompressedCertNode::Lit { lit, .. } => {
            add_expanded_bytes(&mut bytes, literal_owned_bytes(lit))?;
        }
        CompressedCertNode::MData { metadata, .. } => {
            add_sized_payload(
                &mut bytes,
                metadata.len(),
                size_of::<<MDataMap as IntoIterator>::Item>(),
            )?;
        }
        _ => {}
    }
    Ok(bytes)
}

fn add_def_eq_step_cost(root: &DefEqStep, total: &mut ExpandedCost) -> Result<(), DecompressError> {
    let mut pending = vec![root];
    while let Some(step) = pending.pop() {
        add_expanded_nodes(&mut total.nodes, 1)?;
        add_expanded_bytes(&mut total.bytes, size_of::<DefEqStep>())?;
        match step {
            DefEqStep::Symm(inner) => pending.push(inner),
            DefEqStep::Trans(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            DefEqStep::Struct(name, children) => {
                add_expanded_bytes(&mut total.bytes, name.len())?;
                if children.len() > MAX_DECOMPRESSED_CERT_NODES.saturating_sub(total.nodes) {
                    return Err(DecompressError::ExpandedCertLimit {
                        nodes: MAX_DECOMPRESSED_CERT_NODES.saturating_add(1),
                        max: MAX_DECOMPRESSED_CERT_NODES,
                    });
                }
                pending.extend(children);
            }
            DefEqStep::Refl
            | DefEqStep::Beta
            | DefEqStep::Delta(_)
            | DefEqStep::Zeta
            | DefEqStep::Iota => {}
        }
    }
    Ok(())
}

fn add_embedded_cert_cost(
    root: &ProofCert,
    total: &mut ExpandedCost,
) -> Result<(), DecompressError> {
    let mut pending = vec![root];
    while let Some(cert) = pending.pop() {
        add_expanded_nodes(&mut total.nodes, 1)?;
        add_expanded_bytes(&mut total.bytes, embedded_cert_local_bytes(cert)?)?;
        match cert {
            ProofCert::App {
                fn_cert, arg_cert, ..
            }
            | ProofCert::Lam {
                arg_type_cert: fn_cert,
                body_cert: arg_cert,
                ..
            }
            | ProofCert::Pi {
                arg_type_cert: fn_cert,
                body_type_cert: arg_cert,
                ..
            }
            | ProofCert::CubicalPathApp {
                path_cert: fn_cert,
                arg_cert,
                ..
            }
            | ProofCert::ZFCMem {
                elem_cert: fn_cert,
                set_cert: arg_cert,
            }
            | ProofCert::ZFCComprehension {
                var_ty_cert: fn_cert,
                pred_cert: arg_cert,
                ..
            } => {
                pending.push(fn_cert);
                pending.push(arg_cert);
            }
            ProofCert::Let {
                type_cert,
                value_cert,
                body_cert,
                ..
            } => {
                pending.push(type_cert);
                pending.push(value_cert);
                pending.push(body_cert);
            }
            ProofCert::DefEq {
                inner, eq_steps, ..
            } => {
                pending.push(inner);
                for step in eq_steps {
                    add_def_eq_step_cost(step, total)?;
                }
            }
            ProofCert::MData { inner_cert, .. }
            | ProofCert::Proj {
                expr_cert: inner_cert,
                ..
            }
            | ProofCert::CubicalPathLam {
                body_cert: inner_cert,
                ..
            }
            | ProofCert::Squash { inner_cert } => pending.push(inner_cert),
            ProofCert::CubicalPath {
                ty_cert,
                left_cert,
                right_cert,
                ..
            }
            | ProofCert::CubicalTransp {
                ty_cert,
                phi_cert: left_cert,
                base_cert: right_cert,
                ..
            } => {
                pending.push(ty_cert);
                pending.push(left_cert);
                pending.push(right_cert);
            }
            ProofCert::CubicalHComp {
                ty_cert,
                phi_cert,
                u_cert,
                base_cert,
                ..
            }
            | ProofCert::CubicalCoe {
                ty_cert,
                r_cert: phi_cert,
                s_cert: u_cert,
                base_cert,
                ..
            } => {
                pending.push(ty_cert);
                pending.push(phi_cert);
                pending.push(u_cert);
                pending.push(base_cert);
            }
            ProofCert::ZFCSet { kind, .. } => match kind {
                ZFCSetCertKind::Empty | ZFCSetCertKind::Infinity => {}
                ZFCSetCertKind::Singleton(cert)
                | ZFCSetCertKind::Union(cert)
                | ZFCSetCertKind::PowerSet(cert)
                | ZFCSetCertKind::Choice(cert) => pending.push(cert),
                ZFCSetCertKind::Pair(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                ZFCSetCertKind::Separation {
                    set_cert,
                    pred_cert,
                } => {
                    pending.push(set_cert);
                    pending.push(pred_cert);
                }
                ZFCSetCertKind::Replacement {
                    set_cert,
                    func_cert,
                } => {
                    pending.push(set_cert);
                    pending.push(func_cert);
                }
            },
            ProofCert::Sort { .. }
            | ProofCert::BVar { .. }
            | ProofCert::FVar { .. }
            | ProofCert::Const { .. }
            | ProofCert::Lit { .. }
            | ProofCert::CubicalInterval
            | ProofCert::CubicalEndpoint { .. }
            | ProofCert::SProp => {}
        }
    }
    Ok(())
}

fn embedded_cert_local_bytes(cert: &ProofCert) -> Result<usize, DecompressError> {
    let mut bytes = size_of::<ProofCert>();
    match cert {
        ProofCert::BVar { expected_type, .. } => {
            add_embedded_expr_reference_bytes(&mut bytes, expected_type)?;
        }
        ProofCert::FVar { type_, .. } | ProofCert::Lit { type_, .. } => {
            add_embedded_expr_reference_bytes(&mut bytes, type_)?;
        }
        ProofCert::Lam { result_type, .. }
        | ProofCert::Let { result_type, .. }
        | ProofCert::MData { result_type, .. }
        | ProofCert::ZFCSet { result_type, .. }
        | ProofCert::ZFCComprehension { result_type, .. }
        | ProofCert::CubicalHComp { result_type, .. }
        | ProofCert::CubicalTransp { result_type, .. }
        | ProofCert::CubicalCoe { result_type, .. } => {
            add_embedded_expr_reference_bytes(&mut bytes, result_type)?;
        }
        ProofCert::Const { levels, type_, .. } => {
            add_embedded_expr_reference_bytes(&mut bytes, type_)?;
            add_sized_payload(&mut bytes, levels.len(), size_of::<Level>())?;
        }
        ProofCert::App {
            fn_type,
            result_type,
            ..
        }
        | ProofCert::CubicalPathApp {
            path_type: fn_type,
            result_type,
            ..
        }
        | ProofCert::CubicalPathLam {
            body_type: fn_type,
            result_type,
            ..
        } => {
            add_embedded_expr_reference_bytes(&mut bytes, fn_type)?;
            add_embedded_expr_reference_bytes(&mut bytes, result_type)?;
        }
        ProofCert::DefEq {
            expected_type,
            actual_type,
            ..
        } => {
            add_embedded_expr_reference_bytes(&mut bytes, expected_type)?;
            add_embedded_expr_reference_bytes(&mut bytes, actual_type)?;
        }
        ProofCert::Proj {
            expr_type,
            field_type,
            ..
        } => {
            add_embedded_expr_reference_bytes(&mut bytes, expr_type)?;
            add_embedded_expr_reference_bytes(&mut bytes, field_type)?;
        }
        ProofCert::Sort { .. }
        | ProofCert::Pi { .. }
        | ProofCert::CubicalInterval
        | ProofCert::CubicalEndpoint { .. }
        | ProofCert::CubicalPath { .. }
        | ProofCert::ZFCMem { .. }
        | ProofCert::SProp
        | ProofCert::Squash { .. } => {}
    }
    match cert {
        ProofCert::Lit { lit, .. } => {
            add_expanded_bytes(&mut bytes, literal_owned_bytes(lit))?;
        }
        ProofCert::MData { metadata, .. } => {
            add_sized_payload(
                &mut bytes,
                metadata.len(),
                size_of::<<MDataMap as IntoIterator>::Item>(),
            )?;
        }
        _ => {}
    }
    Ok(bytes)
}

fn embedded_expr_local_owned_bytes(expr: &Expr) -> usize {
    match &expr.kind {
        ExprKind::Const(_, levels) => levels.len().saturating_mul(size_of::<Level>()),
        ExprKind::Lit(literal) => literal_owned_bytes(literal),
        ExprKind::MData(metadata, _) => metadata
            .len()
            .saturating_mul(size_of::<<MDataMap as IntoIterator>::Item>()),
        _ => 0,
    }
}

fn add_embedded_expr_reference_bytes(
    bytes: &mut usize,
    expr: &Expr,
) -> Result<(), DecompressError> {
    add_expanded_bytes(bytes, size_of::<Expr>())?;
    add_expanded_bytes(bytes, embedded_expr_local_owned_bytes(expr))
}

fn validate_level_index(compressed: &CompressedCert, idx: LevelIdx) -> Result<(), DecompressError> {
    if (idx as usize) < compressed.levels.len() {
        Ok(())
    } else {
        Err(DecompressError::InvalidLevelIndex(idx))
    }
}

fn validate_expr_index(compressed: &CompressedCert, idx: ExprIdx) -> Result<(), DecompressError> {
    if (idx as usize) < compressed.exprs.len() {
        Ok(())
    } else {
        Err(DecompressError::InvalidExprIndex(idx))
    }
}

fn validate_cert_index(compressed: &CompressedCert, idx: CertIdx) -> Result<(), DecompressError> {
    if (idx as usize) < compressed.certs.len() {
        Ok(())
    } else {
        Err(DecompressError::InvalidCertIndex(idx))
    }
}

fn validate_prior_level(
    compressed: &CompressedCert,
    parent: LevelIdx,
    child: LevelIdx,
) -> Result<(), DecompressError> {
    validate_level_index(compressed, child)?;
    validate_prior("level", parent, child)
}

fn validate_prior_expr(
    compressed: &CompressedCert,
    parent: ExprIdx,
    child: ExprIdx,
) -> Result<(), DecompressError> {
    validate_expr_index(compressed, child)?;
    validate_prior("expression", parent, child)
}

fn validate_prior_cert(
    compressed: &CompressedCert,
    parent: CertIdx,
    child: CertIdx,
) -> Result<(), DecompressError> {
    validate_cert_index(compressed, child)?;
    validate_prior("certificate", parent, child)
}

fn validate_prior(table: &'static str, parent: u32, child: u32) -> Result<(), DecompressError> {
    if child < parent {
        Ok(())
    } else {
        Err(DecompressError::NonCanonicalReference {
            table,
            parent,
            child,
        })
    }
}

/// Decompress a compressed certificate back to the original format.
pub fn decompress_cert(compressed: &CompressedCert) -> Result<ProofCert, DecompressError> {
    validate_compressed(compressed)?;
    let mut state = DecompressionState::new(compressed);
    state.decompress_cert(compressed.root)
}
