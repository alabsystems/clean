// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hash-consing compression for proof certificates.
//!
//! Interns expressions, levels, and certificates into deduplicated tables
//! for structure-sharing compression.

use crate::expr::{stack_safe, Expr, ExprKind};
use crate::level::Level;

use std::{
    collections::{hash_map::DefaultHasher, HashMap},
    hash::{Hash, Hasher},
};

use super::super::{DefEqStep, ProofCert};
use super::compress_hash::expr_name;
use super::types::{
    CertIdx, CompressedCert, CompressedCertNode, CompressedCertSchema, CompressedExpr,
    CompressedLevel, CompressionStats, ExprIdx, LevelIdx,
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

fn hash_value<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn hash_compressed_cert_node(node: &CompressedCertNode) -> u64 {
    let mut hasher = DefaultHasher::new();
    match node {
        CompressedCertNode::Sort { level } => {
            0_u8.hash(&mut hasher);
            level.hash(&mut hasher);
        }
        CompressedCertNode::BVar { idx, expected_type } => {
            1_u8.hash(&mut hasher);
            idx.hash(&mut hasher);
            expected_type.hash(&mut hasher);
        }
        CompressedCertNode::FVar { id, type_ } => {
            2_u8.hash(&mut hasher);
            id.hash(&mut hasher);
            type_.hash(&mut hasher);
        }
        CompressedCertNode::Const {
            name,
            levels,
            type_,
        } => {
            3_u8.hash(&mut hasher);
            name.hash(&mut hasher);
            levels.hash(&mut hasher);
            type_.hash(&mut hasher);
        }
        CompressedCertNode::App {
            fn_cert,
            fn_type,
            arg_cert,
            result_type,
        } => {
            4_u8.hash(&mut hasher);
            fn_cert.hash(&mut hasher);
            fn_type.hash(&mut hasher);
            arg_cert.hash(&mut hasher);
            result_type.hash(&mut hasher);
        }
        CompressedCertNode::Lam {
            binder_info,
            arg_type_cert,
            body_cert,
            result_type,
        } => {
            5_u8.hash(&mut hasher);
            binder_info.hash(&mut hasher);
            arg_type_cert.hash(&mut hasher);
            body_cert.hash(&mut hasher);
            result_type.hash(&mut hasher);
        }
        CompressedCertNode::Pi {
            binder_info,
            arg_type_cert,
            arg_level,
            body_type_cert,
            body_level,
        } => {
            6_u8.hash(&mut hasher);
            binder_info.hash(&mut hasher);
            arg_type_cert.hash(&mut hasher);
            arg_level.hash(&mut hasher);
            body_type_cert.hash(&mut hasher);
            body_level.hash(&mut hasher);
        }
        CompressedCertNode::Let {
            type_cert,
            value_cert,
            body_cert,
            result_type,
        } => {
            7_u8.hash(&mut hasher);
            type_cert.hash(&mut hasher);
            value_cert.hash(&mut hasher);
            body_cert.hash(&mut hasher);
            result_type.hash(&mut hasher);
        }
        CompressedCertNode::Lit { lit, type_ } => {
            8_u8.hash(&mut hasher);
            lit.hash(&mut hasher);
            type_.hash(&mut hasher);
        }
        CompressedCertNode::DefEq {
            inner,
            expected_type,
            actual_type,
            eq_steps,
        } => {
            9_u8.hash(&mut hasher);
            inner.hash(&mut hasher);
            expected_type.hash(&mut hasher);
            actual_type.hash(&mut hasher);
            hash_def_eq_steps(eq_steps, &mut hasher);
        }
        CompressedCertNode::MData {
            metadata,
            inner_cert,
            result_type,
        } => {
            10_u8.hash(&mut hasher);
            metadata.hash(&mut hasher);
            inner_cert.hash(&mut hasher);
            result_type.hash(&mut hasher);
        }
        CompressedCertNode::Proj {
            struct_name,
            idx,
            expr_cert,
            expr_type,
            field_type,
        } => {
            11_u8.hash(&mut hasher);
            struct_name.hash(&mut hasher);
            idx.hash(&mut hasher);
            expr_cert.hash(&mut hasher);
            expr_type.hash(&mut hasher);
            field_type.hash(&mut hasher);
        }
        CompressedCertNode::ModeSpecific(_) => {
            // Mode-specific nodes are deliberately not hash-consed: their
            // payload remains an owned recursive ProofCert.
            12_u8.hash(&mut hasher);
        }
    }
    hasher.finish()
}

fn hash_def_eq_steps(roots: &[DefEqStep], hasher: &mut DefaultHasher) {
    roots.len().hash(hasher);
    let mut pending: Vec<&DefEqStep> = roots.iter().rev().collect();
    while let Some(step) = pending.pop() {
        match step {
            DefEqStep::Refl => 0_u8.hash(hasher),
            DefEqStep::Symm(inner) => {
                1_u8.hash(hasher);
                pending.push(inner);
            }
            DefEqStep::Trans(left, right) => {
                2_u8.hash(hasher);
                pending.push(right);
                pending.push(left);
            }
            DefEqStep::Beta => 3_u8.hash(hasher),
            DefEqStep::Delta(name) => {
                4_u8.hash(hasher);
                name.hash(hasher);
            }
            DefEqStep::Zeta => 5_u8.hash(hasher),
            DefEqStep::Iota => 6_u8.hash(hasher),
            DefEqStep::Struct(name, children) => {
                7_u8.hash(hasher);
                name.hash(hasher);
                children.len().hash(hasher);
                pending.extend(children.iter().rev());
            }
        }
    }
}

/// State for certificate compression (hash-consing)
pub(crate) struct CompressionState {
    expr_map: HashMap<u64, Vec<ExprIdx>>,
    pub(crate) exprs: Vec<CompressedExpr>,
    level_map: HashMap<u64, Vec<LevelIdx>>,
    pub(crate) levels: Vec<CompressedLevel>,
    cert_map: HashMap<u64, Vec<CertIdx>>,
    pub(crate) certs: Vec<CompressedCertNode>,
    level_identity_map: HashMap<usize, LevelIdx>,
    expr_identity_map: HashMap<usize, ExprIdx>,
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
            level_identity_map: HashMap::new(),
            expr_identity_map: HashMap::new(),
        }
    }

    #[inline]
    fn len_to_idx(len: usize) -> Result<u32, CompressError> {
        u32::try_from(len).map_err(|_| CompressError::Overflow { count: len })
    }

    // ---- Interning methods ----

    pub(crate) fn intern_level(&mut self, level: &Level) -> Result<LevelIdx, CompressError> {
        stack_safe(|| self.intern_level_impl(level))
    }

    fn intern_level_impl(&mut self, level: &Level) -> Result<LevelIdx, CompressError> {
        let identity = std::ptr::from_ref(level) as usize;
        if let Some(&idx) = self.level_identity_map.get(&identity) {
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

        let hash = hash_value(&compressed);
        let idx = self.intern_compressed_level(hash, compressed)?;
        self.level_identity_map.insert(identity, idx);
        Ok(idx)
    }

    fn intern_compressed_level(
        &mut self,
        hash: u64,
        compressed: CompressedLevel,
    ) -> Result<LevelIdx, CompressError> {
        if let Some(candidates) = self.level_map.get(&hash) {
            for &idx in candidates {
                if self.levels[idx as usize] == compressed {
                    return Ok(idx);
                }
            }
        }

        let idx = Self::len_to_idx(self.levels.len())?;
        self.levels.push(compressed);
        self.level_map.entry(hash).or_default().push(idx);
        Ok(idx)
    }

    pub(crate) fn intern_expr(&mut self, expr: &Expr) -> Result<ExprIdx, CompressError> {
        stack_safe(|| self.intern_expr_impl(expr))
    }

    fn intern_expr_impl(&mut self, expr: &Expr) -> Result<ExprIdx, CompressError> {
        let identity = std::ptr::from_ref(expr) as usize;
        if let Some(&idx) = self.expr_identity_map.get(&identity) {
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
            ExprKind::Lam(binder, ty, body) => {
                CompressedExpr::Lam(*binder, self.intern_expr(ty)?, self.intern_expr(body)?)
            }
            ExprKind::Pi(binder, ty, body) => {
                CompressedExpr::Pi(*binder, self.intern_expr(ty)?, self.intern_expr(body)?)
            }
            ExprKind::Let(name, ty, val, body, non_dep) => CompressedExpr::Let(
                name.clone(),
                self.intern_expr(ty)?,
                self.intern_expr(val)?,
                self.intern_expr(body)?,
                *non_dep,
            ),
            ExprKind::Lit(lit) => CompressedExpr::Lit(lit.clone()),
            ExprKind::Proj(n, idx, e) => {
                CompressedExpr::Proj(n.clone(), *idx, self.intern_expr(e)?)
            }
            ExprKind::MData(md, e) => CompressedExpr::MData(md.clone(), self.intern_expr(e)?),
            // Mode-specific extensions: no compressed representation
            _ => return Err(CompressError::UnsupportedExprKind(expr_name(expr))),
        };

        let hash = hash_value(&compressed);
        let idx = self.intern_compressed_expr(hash, compressed)?;
        self.expr_identity_map.insert(identity, idx);
        Ok(idx)
    }

    fn intern_compressed_expr(
        &mut self,
        hash: u64,
        compressed: CompressedExpr,
    ) -> Result<ExprIdx, CompressError> {
        if let Some(candidates) = self.expr_map.get(&hash) {
            for &idx in candidates {
                if self.exprs[idx as usize] == compressed {
                    return Ok(idx);
                }
            }
        }

        let idx = Self::len_to_idx(self.exprs.len())?;
        self.exprs.push(compressed);
        self.expr_map.entry(hash).or_default().push(idx);
        Ok(idx)
    }

    pub(crate) fn intern_cert(&mut self, cert: &ProofCert) -> Result<CertIdx, CompressError> {
        stack_safe(|| self.intern_cert_impl(cert))
    }

    fn intern_cert_impl(&mut self, cert: &ProofCert) -> Result<CertIdx, CompressError> {
        let compressed = self.intern_cert_node(cert)?;

        if matches!(compressed, CompressedCertNode::ModeSpecific(_)) {
            let idx = Self::len_to_idx(self.certs.len())?;
            self.certs.push(compressed);
            return Ok(idx);
        }
        let hash = hash_compressed_cert_node(&compressed);
        self.intern_compressed_cert(hash, compressed)
    }

    fn intern_compressed_cert(
        &mut self,
        hash: u64,
        compressed: CompressedCertNode,
    ) -> Result<CertIdx, CompressError> {
        if let Some(candidates) = self.cert_map.get(&hash) {
            for &idx in candidates {
                if self.certs[idx as usize] == compressed {
                    return Ok(idx);
                }
            }
        }

        let idx = Self::len_to_idx(self.certs.len())?;
        self.certs.push(compressed);
        self.cert_map.entry(hash).or_default().push(idx);
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
        schema: CompressedCertSchema::current(),
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

#[cfg(test)]
mod collision_tests {
    use super::*;
    use crate::expr::{BinderData, BinderInfo, Multiplicity};

    #[test]
    fn forced_hash_collisions_never_alias_distinct_nodes() {
        const COLLISION: u64 = 0x5eed;
        let mut state = CompressionState::new();

        let level_zero = state
            .intern_compressed_level(COLLISION, CompressedLevel::Zero)
            .unwrap();
        let level_succ = state
            .intern_compressed_level(COLLISION, CompressedLevel::Succ(level_zero))
            .unwrap();
        let level_zero_again = state
            .intern_compressed_level(COLLISION, CompressedLevel::Zero)
            .unwrap();
        assert_eq!(level_zero, level_zero_again);
        assert_ne!(level_zero, level_succ);

        let expr_zero = state
            .intern_compressed_expr(COLLISION, CompressedExpr::BVar(0))
            .unwrap();
        let expr_one = state
            .intern_compressed_expr(COLLISION, CompressedExpr::BVar(1))
            .unwrap();
        let expr_zero_again = state
            .intern_compressed_expr(COLLISION, CompressedExpr::BVar(0))
            .unwrap();
        assert_eq!(expr_zero, expr_zero_again);
        assert_ne!(expr_zero, expr_one);

        let linear_binder = BinderData::new(BinderInfo::Default, Multiplicity::One);
        let unrestricted_binder = BinderData::new(BinderInfo::Default, Multiplicity::Many);
        let linear_lam = state
            .intern_compressed_expr(
                COLLISION,
                CompressedExpr::Lam(linear_binder, expr_zero, expr_one),
            )
            .unwrap();
        let unrestricted_lam = state
            .intern_compressed_expr(
                COLLISION,
                CompressedExpr::Lam(unrestricted_binder, expr_zero, expr_one),
            )
            .unwrap();
        assert_ne!(linear_lam, unrestricted_lam);

        let named_let = state
            .intern_compressed_expr(
                COLLISION,
                CompressedExpr::Let(
                    crate::name::Name::from_string("kept"),
                    expr_zero,
                    expr_one,
                    expr_zero,
                    true,
                ),
            )
            .unwrap();
        let anonymous_let = state
            .intern_compressed_expr(
                COLLISION,
                CompressedExpr::Let(
                    crate::name::Name::anon(),
                    expr_zero,
                    expr_one,
                    expr_zero,
                    false,
                ),
            )
            .unwrap();
        assert_ne!(named_let, anonymous_let);

        let cert_zero = state
            .intern_compressed_cert(COLLISION, CompressedCertNode::Sort { level: level_zero })
            .unwrap();
        let cert_succ = state
            .intern_compressed_cert(COLLISION, CompressedCertNode::Sort { level: level_succ })
            .unwrap();
        let cert_zero_again = state
            .intern_compressed_cert(COLLISION, CompressedCertNode::Sort { level: level_zero })
            .unwrap();
        assert_eq!(cert_zero, cert_zero_again);
        assert_ne!(cert_zero, cert_succ);

        assert_eq!(state.level_map[&COLLISION], vec![level_zero, level_succ]);
        assert_eq!(
            state.expr_map[&COLLISION],
            vec![
                expr_zero,
                expr_one,
                linear_lam,
                unrestricted_lam,
                named_let,
                anonymous_let,
            ]
        );
        assert_eq!(state.cert_map[&COLLISION], vec![cert_zero, cert_succ]);
    }
}
