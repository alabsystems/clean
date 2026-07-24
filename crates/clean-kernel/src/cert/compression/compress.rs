// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hash-consing compression for proof certificates.
//!
//! Interns expressions, levels, and certificates into deduplicated tables
//! for structure-sharing compression.

use crate::expr::{Expr, ExprKind};
use crate::level::Level;

use std::collections::HashMap;

use super::super::ProofCert;
use super::compress_hash::{expr_name, hash_cert, hash_expr, hash_level};
use super::types::{
    CertIdx, CompressedCert, CompressedCertNode, CompressedExpr, CompressedLevel, CompressionStats,
    ExprIdx, LevelIdx,
};

/// Error during certificate compression
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum CompressError {
    /// Expression kind has no compressed representation
    #[error("Mode-specific expression has no compressed representation: {0}")]
    UnsupportedExprKind(String),
    /// Table size exceeds u32::MAX
    #[error("Table size {count} exceeds u32::MAX")]
    Overflow {
        /// Actual count that overflowed
        count: usize,
    },
}

/// State for certificate compression (hash-consing)
pub(crate) struct CompressionState {
    expr_map: HashMap<u64, ExprIdx>,
    pub(crate) exprs: Vec<CompressedExpr>,
    level_map: HashMap<u64, LevelIdx>,
    pub(crate) levels: Vec<CompressedLevel>,
    cert_map: HashMap<u64, CertIdx>,
    pub(crate) certs: Vec<CompressedCertNode>,
}

impl CompressionState {
    pub(crate) fn new() -> Self {
        Self {
            expr_map: HashMap::new(),
            exprs: Vec::new(),
            level_map: HashMap::new(),
            levels: Vec::new(),
            cert_map: HashMap::new(),
            certs: Vec::new(),
        }
    }

    #[inline]
    fn len_to_idx(len: usize) -> Result<u32, CompressError> {
        u32::try_from(len).map_err(|_| CompressError::Overflow { count: len })
    }

    // ---- Interning methods ----

    pub(crate) fn intern_level(&mut self, level: &Level) -> Result<LevelIdx, CompressError> {
        let hash = hash_level(level);
        if let Some(&idx) = self.level_map.get(&hash) {
            return Ok(idx);
        }

        let compressed = match level {
            Level::Zero => CompressedLevel::Zero,
            Level::Succ(l) => CompressedLevel::Succ(self.intern_level(l)?),
            Level::Max(l1, l2) => {
                let i1 = self.intern_level(l1)?;
                let i2 = self.intern_level(l2)?;
                CompressedLevel::Max(i1, i2)
            }
            Level::IMax(l1, l2) => {
                let i1 = self.intern_level(l1)?;
                let i2 = self.intern_level(l2)?;
                CompressedLevel::IMax(i1, i2)
            }
            Level::Param(n) => CompressedLevel::Param(n.clone()),
        };

        let idx = Self::len_to_idx(self.levels.len())?;
        self.levels.push(compressed);
        self.level_map.insert(hash, idx);
        Ok(idx)
    }

    pub(crate) fn intern_expr(&mut self, expr: &Expr) -> Result<ExprIdx, CompressError> {
        let hash = hash_expr(expr);
        if let Some(&idx) = self.expr_map.get(&hash) {
            return Ok(idx);
        }

        let compressed = match &expr.kind {
            ExprKind::BVar(idx) => CompressedExpr::BVar(*idx),
            ExprKind::FVar(id) => CompressedExpr::FVar(*id),
            ExprKind::Sort(l) => CompressedExpr::Sort(self.intern_level(l)?),
            ExprKind::Const(n, ls) => {
                let lvls: Result<Vec<_>, _> = ls.iter().map(|l| self.intern_level(l)).collect();
                CompressedExpr::Const(n.clone(), lvls?)
            }
            ExprKind::App(f, a) => CompressedExpr::App(self.intern_expr(f)?, self.intern_expr(a)?),
            ExprKind::Lam(bi, ty, body) => {
                CompressedExpr::Lam(bi.info, self.intern_expr(ty)?, self.intern_expr(body)?)
            }
            ExprKind::Pi(bi, ty, body) => {
                CompressedExpr::Pi(bi.info, self.intern_expr(ty)?, self.intern_expr(body)?)
            }
            ExprKind::Let(_, ty, val, body, _) => CompressedExpr::Let(
                self.intern_expr(ty)?,
                self.intern_expr(val)?,
                self.intern_expr(body)?,
            ),
            ExprKind::Lit(lit) => CompressedExpr::Lit(lit.clone()),
            ExprKind::Proj(n, idx, e) => {
                CompressedExpr::Proj(n.clone(), *idx, self.intern_expr(e)?)
            }
            ExprKind::MData(md, e) => CompressedExpr::MData(md.clone(), self.intern_expr(e)?),
            // Mode-specific extensions: no compressed representation
            _ => return Err(CompressError::UnsupportedExprKind(expr_name(expr))),
        };

        let idx = Self::len_to_idx(self.exprs.len())?;
        self.exprs.push(compressed);
        self.expr_map.insert(hash, idx);
        Ok(idx)
    }

    pub(crate) fn intern_cert(&mut self, cert: &ProofCert) -> Result<CertIdx, CompressError> {
        let hash = hash_cert(cert);
        if let Some(&idx) = self.cert_map.get(&hash) {
            return Ok(idx);
        }

        let compressed = self.intern_cert_node(cert)?;

        let idx = Self::len_to_idx(self.certs.len())?;
        self.certs.push(compressed);
        self.cert_map.insert(hash, idx);
        Ok(idx)
    }

    /// Intern core certificate variants (Sort through Lam).
    fn intern_cert_node(&mut self, cert: &ProofCert) -> Result<CompressedCertNode, CompressError> {
        match cert {
            ProofCert::Sort { level } => Ok(CompressedCertNode::Sort {
                level: self.intern_level(level)?,
            }),
            ProofCert::BVar { idx, expected_type } => Ok(CompressedCertNode::BVar {
                idx: *idx,
                expected_type: self.intern_expr(expected_type)?,
            }),
            ProofCert::FVar { id, type_ } => Ok(CompressedCertNode::FVar {
                id: *id,
                type_: self.intern_expr(type_)?,
            }),
            ProofCert::Const {
                name,
                levels,
                type_,
            } => {
                let lvls: Result<Vec<_>, _> = levels.iter().map(|l| self.intern_level(l)).collect();
                Ok(CompressedCertNode::Const {
                    name: name.clone(),
                    levels: lvls?,
                    type_: self.intern_expr(type_)?,
                })
            }
            ProofCert::App {
                fn_cert,
                fn_type,
                arg_cert,
                result_type,
            } => Ok(CompressedCertNode::App {
                fn_cert: self.intern_cert(fn_cert)?,
                fn_type: self.intern_expr(fn_type)?,
                arg_cert: self.intern_cert(arg_cert)?,
                result_type: self.intern_expr(result_type)?,
            }),
            ProofCert::Lam {
                binder_info,
                arg_type_cert,
                body_cert,
                result_type,
            } => Ok(CompressedCertNode::Lam {
                binder_info: *binder_info,
                arg_type_cert: self.intern_cert(arg_type_cert)?,
                body_cert: self.intern_cert(body_cert)?,
                result_type: self.intern_expr(result_type)?,
            }),
            _ => self.intern_cert_node_ext(cert),
        }
    }

    /// Intern compound certificate variants (Pi through ModeSpecific).
    fn intern_cert_node_ext(
        &mut self,
        cert: &ProofCert,
    ) -> Result<CompressedCertNode, CompressError> {
        match cert {
            ProofCert::Pi {
                binder_info,
                arg_type_cert,
                arg_level,
                body_type_cert,
                body_level,
            } => Ok(CompressedCertNode::Pi {
                binder_info: *binder_info,
                arg_type_cert: self.intern_cert(arg_type_cert)?,
                arg_level: self.intern_level(arg_level)?,
                body_type_cert: self.intern_cert(body_type_cert)?,
                body_level: self.intern_level(body_level)?,
            }),
            ProofCert::Let {
                type_cert,
                value_cert,
                body_cert,
                result_type,
            } => Ok(CompressedCertNode::Let {
                type_cert: self.intern_cert(type_cert)?,
                value_cert: self.intern_cert(value_cert)?,
                body_cert: self.intern_cert(body_cert)?,
                result_type: self.intern_expr(result_type)?,
            }),
            ProofCert::Lit { lit, type_ } => Ok(CompressedCertNode::Lit {
                lit: lit.clone(),
                type_: self.intern_expr(type_)?,
            }),
            ProofCert::DefEq {
                inner,
                expected_type,
                actual_type,
                eq_steps,
            } => Ok(CompressedCertNode::DefEq {
                inner: self.intern_cert(inner)?,
                expected_type: self.intern_expr(expected_type)?,
                actual_type: self.intern_expr(actual_type)?,
                eq_steps: eq_steps.clone(),
            }),
            ProofCert::MData {
                metadata,
                inner_cert,
                result_type,
            } => Ok(CompressedCertNode::MData {
                metadata: metadata.clone(),
                inner_cert: self.intern_cert(inner_cert)?,
                result_type: self.intern_expr(result_type)?,
            }),
            ProofCert::Proj {
                struct_name,
                idx,
                expr_cert,
                expr_type,
                field_type,
            } => Ok(CompressedCertNode::Proj {
                struct_name: struct_name.clone(),
                idx: *idx,
                expr_cert: self.intern_cert(expr_cert)?,
                expr_type: self.intern_expr(expr_type)?,
                field_type: self.intern_expr(field_type)?,
            }),
            // Mode-specific: store as-is in a boxed ProofCert
            _ => Ok(CompressedCertNode::ModeSpecific(Box::new(cert.clone()))),
        }
    }
}

/// Compress a proof certificate using structure sharing.
pub fn compress_cert(cert: &ProofCert) -> Result<CompressedCert, CompressError> {
    let mut state = CompressionState::new();
    let root = state.intern_cert(cert)?;
    Ok(CompressedCert {
        exprs: state.exprs,
        levels: state.levels,
        certs: state.certs,
        root,
    })
}

/// Compress a certificate and return statistics about the compression.
pub fn compress_cert_with_stats(
    cert: &ProofCert,
) -> Result<(CompressedCert, CompressionStats), CompressError> {
    let compressed = compress_cert(cert)?;

    let original_bytes = bincode::serde::encode_to_vec(cert, bincode::config::standard())
        .map(|v| v.len())
        .unwrap_or(0);
    let compressed_bytes = bincode::serde::encode_to_vec(&compressed, bincode::config::standard())
        .map(|v| v.len())
        .unwrap_or(0);

    let ratio = if compressed_bytes > 0 {
        original_bytes as f64 / compressed_bytes as f64
    } else {
        1.0
    };

    let stats = CompressionStats {
        unique_exprs: compressed.exprs.len(),
        unique_levels: compressed.levels.len(),
        unique_certs: compressed.certs.len(),
        original_bytes,
        compressed_bytes,
        ratio,
    };

    Ok((compressed, stats))
}
