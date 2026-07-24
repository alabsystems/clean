// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hash-consing decompression for proof certificates.
//!
//! Reconstructs original certificate structures from their
//! deduplicated compressed form.

use crate::expr::{Expr, ExprKind, LevelVec};
use crate::level::Level;
use crate::name::Name;

use std::collections::HashMap;
use std::sync::Arc;

use super::super::ProofCert;
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
}

/// State for certificate decompression
pub(crate) struct DecompressionState<'a> {
    compressed: &'a CompressedCert,
    level_cache: HashMap<LevelIdx, Level>,
    expr_cache: HashMap<ExprIdx, Expr>,
    cert_cache: HashMap<CertIdx, ProofCert>,
}

impl<'a> DecompressionState<'a> {
    pub(crate) fn new(compressed: &'a CompressedCert) -> Self {
        Self {
            compressed,
            level_cache: HashMap::new(),
            expr_cache: HashMap::new(),
            cert_cache: HashMap::new(),
        }
    }

    /// Decompress a level by index.
    pub(crate) fn decompress_level(&mut self, idx: LevelIdx) -> Result<Level, DecompressError> {
        if let Some(level) = self.level_cache.get(&idx) {
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

        self.level_cache.insert(idx, level.clone());
        Ok(level)
    }

    /// Decompress an expression by index.
    pub(crate) fn decompress_expr(&mut self, idx: ExprIdx) -> Result<Expr, DecompressError> {
        if let Some(expr) = self.expr_cache.get(&idx) {
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
            CompressedExpr::Lam(bi, ty_idx, body_idx) => {
                let ty = self.decompress_expr(ty_idx)?;
                let body = self.decompress_expr(body_idx)?;
                Expr::from_kind(ExprKind::Lam(bi.into(), ty.into(), body.into()))
            }
            CompressedExpr::Pi(bi, ty_idx, body_idx) => {
                let ty = self.decompress_expr(ty_idx)?;
                let body = self.decompress_expr(body_idx)?;
                Expr::from_kind(ExprKind::Pi(bi.into(), ty.into(), body.into()))
            }
            CompressedExpr::Let(ty_idx, val_idx, body_idx) => {
                let ty = self.decompress_expr(ty_idx)?;
                let val = self.decompress_expr(val_idx)?;
                let body = self.decompress_expr(body_idx)?;
                Expr::from_kind(ExprKind::Let(
                    Name::anon(),
                    ty.into(),
                    val.into(),
                    body.into(),
                    false,
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

        self.expr_cache.insert(idx, expr.clone());
        Ok(expr)
    }

    /// Decompress a certificate by index.
    pub(crate) fn decompress_cert(&mut self, idx: CertIdx) -> Result<ProofCert, DecompressError> {
        if let Some(cert) = self.cert_cache.get(&idx) {
            return Ok(cert.clone());
        }

        let node = self
            .compressed
            .certs
            .get(idx as usize)
            .ok_or(DecompressError::InvalidCertIndex(idx))?
            .clone();

        let cert = self.decompress_cert_node(&node)?;
        self.cert_cache.insert(idx, cert.clone());
        Ok(cert)
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

/// Decompress a compressed certificate back to the original format.
pub fn decompress_cert(compressed: &CompressedCert) -> Result<ProofCert, DecompressError> {
    let mut state = DecompressionState::new(compressed);
    state.decompress_cert(compressed.root)
}
