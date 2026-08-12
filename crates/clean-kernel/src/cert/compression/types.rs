// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compressed certificate types for structure sharing.
//!
//! Defines the compressed representation of proof certificates using index-based
//! references for deduplication (hash-consing).

use crate::expr::{BinderData, BinderInfo, FVarId, Literal, MDataMap};
use crate::name::Name;

use serde::{Deserialize, Deserializer, Serialize};

use super::super::{DefEqStep, ProofCert};

/// Index into the expression table in compressed format
pub type ExprIdx = u32;

/// Index into the level table in compressed format
pub type LevelIdx = u32;

/// Index into the certificate table in compressed format
pub type CertIdx = u32;

/// Validated raw-wire schema discriminator for [`CompressedCert`].
///
/// This is the first serialized field, so schema-less v1 bytes are rejected
/// before any expression, level, or certificate table is materialized.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CompressedCertSchema {
    magic: [u8; 4],
    version: u8,
}

impl CompressedCertSchema {
    /// Raw compressed-certificate magic.
    pub const MAGIC: [u8; 4] = *b"L5CC";
    /// Version 2 preserves full binder and let-binding metadata.
    pub const VERSION: u8 = 2;

    /// Current validated schema header.
    #[must_use]
    pub const fn current() -> Self {
        Self {
            magic: Self::MAGIC,
            version: Self::VERSION,
        }
    }

    pub(crate) fn is_current(self) -> bool {
        self == Self::current()
    }
}

impl<'de> Deserialize<'de> for CompressedCertSchema {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        struct WireSchema {
            magic: [u8; 4],
            version: u8,
        }

        let wire = WireSchema::deserialize(deserializer)?;
        if wire.magic != Self::MAGIC {
            return Err(serde::de::Error::custom(
                "invalid raw compressed-certificate schema magic",
            ));
        }
        if wire.version != Self::VERSION {
            return Err(serde::de::Error::custom(format!(
                "unsupported raw compressed-certificate schema version {}; expected {}",
                wire.version,
                Self::VERSION
            )));
        }
        Ok(Self::current())
    }
}

/// Compressed proof certificate format using structure sharing.
///
/// This format deduplicates repeated subexpressions, levels, and certificates
/// to achieve significant size reduction for large proofs.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CompressedCert {
    /// Validated raw-wire schema discriminator.
    pub schema: CompressedCertSchema,
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
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
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
    Lam(BinderData, ExprIdx, ExprIdx),
    /// Pi (forall) type: binder info, domain type index, codomain index
    Pi(BinderData, ExprIdx, ExprIdx),
    /// Let binding: type index, value index, body index
    Let(Name, ExprIdx, ExprIdx, ExprIdx, bool),
    /// Literal value (nat/string)
    Lit(Literal),
    /// Projection: struct name, field index, struct expr index
    Proj(Name, u32, ExprIdx),
    /// Metadata wrapper: metadata map, inner expr index
    MData(MDataMap, ExprIdx),
}

/// Compressed universe level with indices for nested levels
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
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

#[cfg(test)]
mod schema_tests {
    use super::*;
    use crate::cert::compression::limits::decode_certificate_bincode_limited;

    #[derive(Serialize)]
    struct SchemaLessV1 {
        exprs: Vec<CompressedExpr>,
        levels: Vec<CompressedLevel>,
        certs: Vec<CompressedCertNode>,
        root: CertIdx,
    }

    #[test]
    fn raw_schema_rejects_schema_less_v1_before_table_decode() {
        let legacy = SchemaLessV1 {
            exprs: vec![],
            levels: vec![CompressedLevel::Zero],
            certs: vec![CompressedCertNode::Sort { level: 0 }],
            root: 0,
        };
        let bytes = bincode::serde::encode_to_vec(&legacy, bincode::config::standard()).unwrap();
        let error = decode_certificate_bincode_limited::<CompressedCert>(&bytes).unwrap_err();
        assert!(
            error.contains("schema") || error.contains("UnexpectedEnd"),
            "unexpected legacy-wire error: {error}"
        );
    }

    #[test]
    fn current_raw_schema_roundtrips() {
        let current = CompressedCert {
            schema: CompressedCertSchema::current(),
            exprs: vec![],
            levels: vec![CompressedLevel::Zero],
            certs: vec![CompressedCertNode::Sort { level: 0 }],
            root: 0,
        };
        let bytes = bincode::serde::encode_to_vec(&current, bincode::config::standard()).unwrap();
        let decoded: CompressedCert = decode_certificate_bincode_limited(&bytes).unwrap();
        assert_eq!(decoded, current);
    }
}
