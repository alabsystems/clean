// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compressed certificate types for structure sharing.
//!
//! Defines the compressed representation of proof certificates using index-based
//! references for deduplication (hash-consing).

use crate::expr::{BinderInfo, FVarId, Literal, MDataMap};
use crate::name::Name;

use serde::{Deserialize, Serialize};

use super::super::{DefEqStep, ProofCert};

/// Index into the expression table in compressed format
pub type ExprIdx = u32;

/// Index into the level table in compressed format
pub type LevelIdx = u32;

/// Index into the certificate table in compressed format
pub type CertIdx = u32;

/// Compressed proof certificate format using structure sharing.
///
/// This format deduplicates repeated subexpressions, levels, and certificates
/// to achieve significant size reduction for large proofs.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CompressedCert {
    /// Deduplicated expression table
    pub exprs: Vec<CompressedExpr>,
    /// Deduplicated level table
    pub levels: Vec<CompressedLevel>,
    /// Deduplicated certificate table
    pub certs: Vec<CompressedCertNode>,
    /// Index of the root certificate
    pub root: CertIdx,
}

/// Compressed expression node with indices instead of nested structures
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompressedExpr {
    /// Bound variable with de Bruijn index
    BVar(u32),
    /// Free variable with unique identifier
    FVar(FVarId),
    /// Sort (Type/Prop) with universe level index
    Sort(LevelIdx),
    /// Constant reference with name and universe level indices
    Const(Name, Vec<LevelIdx>),
    /// Function application: function expr index, argument expr index
    App(ExprIdx, ExprIdx),
    /// Lambda abstraction: binder info, domain type index, body index
    Lam(BinderInfo, ExprIdx, ExprIdx),
    /// Pi (forall) type: binder info, domain type index, codomain index
    Pi(BinderInfo, ExprIdx, ExprIdx),
    /// Let binding: type index, value index, body index
    Let(ExprIdx, ExprIdx, ExprIdx),
    /// Literal value (nat/string)
    Lit(Literal),
    /// Projection: struct name, field index, struct expr index
    Proj(Name, u32, ExprIdx),
    /// Metadata wrapper: metadata map, inner expr index
    MData(MDataMap, ExprIdx),
}

/// Compressed universe level with indices for nested levels
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompressedLevel {
    /// Universe level zero (Prop)
    Zero,
    /// Successor level: index of base level
    Succ(LevelIdx),
    /// Maximum of two levels: indices of both levels
    Max(LevelIdx, LevelIdx),
    /// Impredicative maximum: indices of both levels
    IMax(LevelIdx, LevelIdx),
    /// Named universe parameter
    Param(Name),
}

/// Compressed certificate node with indices
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum CompressedCertNode {
    /// Certificate for Sort expressions
    Sort {
        /// Universe level index
        level: LevelIdx,
    },
    /// Certificate for bound variables
    BVar {
        /// De Bruijn index
        idx: u32,
        /// Expected type expression index
        expected_type: ExprIdx,
    },
    /// Certificate for free variables
    FVar {
        /// Free variable identifier
        id: FVarId,
        /// Type expression index
        type_: ExprIdx,
    },
    /// Certificate for constant references
    Const {
        /// Constant name
        name: Name,
        /// Universe level indices
        levels: Vec<LevelIdx>,
        /// Type expression index
        type_: ExprIdx,
    },
    /// Certificate for function application
    App {
        /// Function certificate index
        fn_cert: CertIdx,
        /// Function type expression index
        fn_type: ExprIdx,
        /// Argument certificate index
        arg_cert: CertIdx,
        /// Result type expression index
        result_type: ExprIdx,
    },
    /// Certificate for lambda abstraction
    Lam {
        /// Binder info (implicit/explicit)
        binder_info: BinderInfo,
        /// Argument type certificate index
        arg_type_cert: CertIdx,
        /// Body certificate index
        body_cert: CertIdx,
        /// Result type expression index
        result_type: ExprIdx,
    },
    /// Certificate for Pi (forall) type
    Pi {
        /// Binder info (implicit/explicit)
        binder_info: BinderInfo,
        /// Argument type certificate index
        arg_type_cert: CertIdx,
        /// Universe level of argument type
        arg_level: LevelIdx,
        /// Body type certificate index
        body_type_cert: CertIdx,
        /// Universe level of body type
        body_level: LevelIdx,
    },
    /// Certificate for let binding
    Let {
        /// Type certificate index
        type_cert: CertIdx,
        /// Value certificate index
        value_cert: CertIdx,
        /// Body certificate index
        body_cert: CertIdx,
        /// Result type expression index
        result_type: ExprIdx,
    },
    /// Certificate for literal values
    Lit {
        /// Literal value
        lit: Literal,
        /// Type expression index
        type_: ExprIdx,
    },
    /// Certificate for definitional equality conversion
    DefEq {
        /// Inner certificate index
        inner: CertIdx,
        /// Expected type expression index
        expected_type: ExprIdx,
        /// Actual type expression index
        actual_type: ExprIdx,
        /// Steps proving definitional equality
        eq_steps: Vec<DefEqStep>,
    },
    /// Certificate for metadata wrapper
    MData {
        /// Metadata map
        metadata: MDataMap,
        /// Inner certificate index
        inner_cert: CertIdx,
        /// Result type expression index
        result_type: ExprIdx,
    },
    /// Certificate for structure projection
    Proj {
        /// Structure type name
        struct_name: Name,
        /// Field index
        idx: u32,
        /// Structure expression certificate index
        expr_cert: CertIdx,
        /// Structure expression type index
        expr_type: ExprIdx,
        /// Projected field type index
        field_type: ExprIdx,
    },
    /// Mode-specific certificates (Cubical, Classical, SetTheoretic)
    /// Stored as boxed ProofCert to avoid duplicating compression logic.
    /// Full compression support for mode-specific certs can be added later.
    ModeSpecific(Box<ProofCert>),
}

/// Statistics about certificate compression
#[derive(Debug, Clone)]
pub struct CompressionStats {
    /// Number of unique expressions in compressed form
    pub unique_exprs: usize,
    /// Number of unique levels in compressed form
    pub unique_levels: usize,
    /// Number of unique certificates in compressed form
    pub unique_certs: usize,
    /// Original size in bytes (bincode serialized)
    pub original_bytes: usize,
    /// Compressed size in bytes (bincode serialized)
    pub compressed_bytes: usize,
    /// Compression ratio (original / compressed)
    pub ratio: f64,
}

impl std::fmt::Display for CompressionStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "CompressionStats {{ exprs: {}, levels: {}, certs: {}, {} -> {} bytes ({:.1}x) }}",
            self.unique_exprs,
            self.unique_levels,
            self.unique_certs,
            self.original_bytes,
            self.compressed_bytes,
            self.ratio
        )
    }
}
