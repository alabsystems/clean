// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate to Polynomial Encoding
//!
//! This module implements encoding of ProofCert trees into polynomials
//! suitable for polynomial commitment schemes.
//!
//! # Encoding Strategy
//!
//! ProofCert trees are flattened to a sequence of field elements:
//! 1. Each node has a tag identifying its variant
//! 2. Node contents are recursively encoded
//! 3. The sequence is interpreted as polynomial evaluations
//! 4. Polynomial is recovered via inverse FFT

use ark_bls12_381::Fr;
use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain,
};

use clean_kernel::cert::{ProofCert, ZFCSetCertKind};
use clean_kernel::name::NameInner;
use clean_kernel::{Expr, Level, Name};

use crate::commit::error::CommitError;

/// Node tag constants for encoding
mod tags {
    // Core certificates (all modes)
    pub const SORT: u64 = 0;
    pub const BVAR: u64 = 1;
    pub const FVAR: u64 = 2;
    pub const CONST: u64 = 3;
    pub const APP: u64 = 4;
    pub const LAM: u64 = 5;
    pub const PI: u64 = 6;
    pub const LET: u64 = 7;
    pub const LIT: u64 = 8;
    pub const DEF_EQ: u64 = 9;
    pub const MDATA: u64 = 10;
    pub const PROJ: u64 = 11;

    // Cubical mode certificates
    pub const CUBICAL_INTERVAL: u64 = 12;
    pub const CUBICAL_ENDPOINT: u64 = 13;
    pub const CUBICAL_PATH: u64 = 14;
    pub const CUBICAL_PATH_LAM: u64 = 15;
    pub const CUBICAL_PATH_APP: u64 = 16;
    pub const CUBICAL_HCOMP: u64 = 17;
    pub const CUBICAL_TRANSP: u64 = 18;
    pub const CUBICAL_COE: u64 = 26;

    // Classical mode certificates (reserved for ClassicalChoice/ClassicalEpsilon encoding)
    #[allow(dead_code)]
    pub const CLASSICAL_CHOICE: u64 = 19;
    #[allow(dead_code)]
    pub const CLASSICAL_EPSILON: u64 = 20;

    // ZFC/Set-theoretic mode certificates
    pub const ZFC_SET: u64 = 21;
    pub const ZFC_MEM: u64 = 22;
    pub const ZFC_COMPREHENSION: u64 = 23;

    // Impredicative mode certificates
    pub const SPROP: u64 = 24;
    pub const SQUASH: u64 = 25;

    // ZFC set construction sub-tags
    pub mod zfc {
        pub const EMPTY: u64 = 0;
        pub const SINGLETON: u64 = 1;
        pub const PAIR: u64 = 2;
        pub const UNION: u64 = 3;
        pub const POWERSET: u64 = 4;
        pub const SEPARATION: u64 = 5;
        pub const REPLACEMENT: u64 = 6;
        pub const INFINITY: u64 = 7;
        pub const CHOICE: u64 = 8;
    }
}

/// Encoded certificate as polynomial and metadata
#[derive(Clone, Debug)]
pub struct EncodedCert {
    /// Polynomial representation
    pub poly: DensePolynomial<Fr>,
    /// Number of field elements in encoding
    pub element_count: usize,
    /// Domain size (power of 2)
    pub domain_size: usize,
}

/// Encode a ProofCert as a polynomial over Fr
///
/// The certificate is flattened to field elements, then interpreted as
/// polynomial evaluations over a suitable domain.
pub fn encode_cert(cert: &ProofCert) -> Result<EncodedCert, CommitError> {
    // Flatten certificate to field elements
    let mut elements = Vec::new();
    flatten_cert(cert, &mut elements)?;

    let element_count = elements.len();

    // Find suitable domain size (power of 2)
    let domain_size = element_count.next_power_of_two();

    // Pad to domain size
    elements.resize(domain_size, Fr::from(0u64));

    // Create evaluation domain
    let domain = GeneralEvaluationDomain::<Fr>::new(domain_size).ok_or_else(|| {
        CommitError::InvalidDegree(format!("Cannot create domain of size {domain_size}"))
    })?;

    // Interpolate polynomial (inverse FFT)
    let coeffs = domain.ifft(&elements);
    let poly = DensePolynomial::from_coefficients_vec(coeffs);

    Ok(EncodedCert {
        poly,
        element_count,
        domain_size,
    })
}

/// Decode a polynomial back to field elements (for verification)
pub fn decode_cert(encoded: &EncodedCert) -> Vec<Fr> {
    let domain = GeneralEvaluationDomain::<Fr>::new(encoded.domain_size)
        .expect("Domain was valid during encoding");

    domain.fft(&encoded.poly.coeffs)
}

/// Flatten a ProofCert into a sequence of field elements
fn flatten_cert(cert: &ProofCert, out: &mut Vec<Fr>) -> Result<(), CommitError> {
    match cert {
        ProofCert::Sort { level } => {
            out.push(Fr::from(tags::SORT));
            flatten_level(level, out);
        }

        ProofCert::BVar { idx, expected_type } => {
            out.push(Fr::from(tags::BVAR));
            out.push(Fr::from(u64::from(*idx)));
            flatten_expr(expected_type, out)?;
        }

        ProofCert::FVar { id, type_ } => {
            out.push(Fr::from(tags::FVAR));
            // Encode FVarId as its raw value
            out.push(Fr::from(id.as_u64()));
            flatten_expr(type_, out)?;
        }

        ProofCert::Const {
            name,
            levels,
            type_,
        } => {
            out.push(Fr::from(tags::CONST));
            flatten_name(name, out);
            out.push(Fr::from(levels.len() as u64));
            for level in levels {
                flatten_level(level, out);
            }
            flatten_expr(type_, out)?;
        }

        ProofCert::App {
            fn_cert,
            fn_type,
            arg_cert,
            result_type,
        } => {
            out.push(Fr::from(tags::APP));
            flatten_cert(fn_cert, out)?;
            flatten_expr(fn_type, out)?;
            flatten_cert(arg_cert, out)?;
            flatten_expr(result_type, out)?;
        }

        ProofCert::Lam {
            binder_info,
            arg_type_cert,
            body_cert,
            result_type,
        } => {
            out.push(Fr::from(tags::LAM));
            out.push(Fr::from(*binder_info as u64));
            flatten_cert(arg_type_cert, out)?;
            flatten_cert(body_cert, out)?;
            flatten_expr(result_type, out)?;
        }

        ProofCert::Pi {
            binder_info,
            arg_type_cert,
            arg_level,
            body_type_cert,
            body_level,
        } => {
            out.push(Fr::from(tags::PI));
            out.push(Fr::from(*binder_info as u64));
            flatten_cert(arg_type_cert, out)?;
            flatten_level(arg_level, out);
            flatten_cert(body_type_cert, out)?;
            flatten_level(body_level, out);
        }

        ProofCert::Let {
            type_cert,
            value_cert,
            body_cert,
            result_type,
        } => {
            out.push(Fr::from(tags::LET));
            flatten_cert(type_cert, out)?;
            flatten_cert(value_cert, out)?;
            flatten_cert(body_cert, out)?;
            flatten_expr(result_type, out)?;
        }

        ProofCert::Lit { lit, type_ } => {
            out.push(Fr::from(tags::LIT));
            // Encode literal value
            match lit {
                clean_kernel::Literal::Nat(n) => {
                    out.push(Fr::from(0u64)); // Nat tag
                                              // Encode arbitrary precision nat from limbs
                    let limbs = n.limbs();
                    // Convert limbs to bytes (each u64 is 8 bytes, little-endian)
                    let num_bytes = limbs.len() * 8;
                    out.push(Fr::from(num_bytes as u64));
                    // Process 31 bytes at a time (fits in Fr field element)
                    let mut byte_idx = 0;
                    while byte_idx < num_bytes {
                        let mut arr = [0u8; 32];
                        let chunk_size = (num_bytes - byte_idx).min(31);
                        for (i, slot) in arr.iter_mut().enumerate().take(chunk_size) {
                            let limb_idx = (byte_idx + i) / 8;
                            let byte_in_limb = (byte_idx + i) % 8;
                            *slot = (limbs[limb_idx] >> (byte_in_limb * 8)) as u8;
                        }
                        out.push(Fr::from_le_bytes_mod_order(&arr));
                        byte_idx += 31;
                    }
                }
                clean_kernel::Literal::String(s) => {
                    out.push(Fr::from(1u64)); // String tag
                    let bytes = s.as_bytes();
                    out.push(Fr::from(bytes.len() as u64));
                    for chunk in bytes.chunks(31) {
                        let mut arr = [0u8; 32];
                        arr[..chunk.len()].copy_from_slice(chunk);
                        out.push(Fr::from_le_bytes_mod_order(&arr));
                    }
                }
            }
            flatten_expr(type_, out)?;
        }

        ProofCert::DefEq {
            inner,
            expected_type,
            actual_type,
            eq_steps,
        } => {
            out.push(Fr::from(tags::DEF_EQ));
            flatten_cert(inner, out)?;
            flatten_expr(expected_type, out)?;
            flatten_expr(actual_type, out)?;
            // Encode eq_steps length (actual steps encoding is complex, simplify for now)
            out.push(Fr::from(eq_steps.len() as u64));
        }

        ProofCert::MData {
            metadata: _,
            inner_cert,
            result_type,
        } => {
            out.push(Fr::from(tags::MDATA));
            // Skip metadata encoding for now (can be extended)
            flatten_cert(inner_cert, out)?;
            flatten_expr(result_type, out)?;
        }

        ProofCert::Proj {
            struct_name,
            idx,
            expr_cert,
            expr_type,
            field_type,
        } => {
            out.push(Fr::from(tags::PROJ));
            flatten_name(struct_name, out);
            out.push(Fr::from(u64::from(*idx)));
            flatten_cert(expr_cert, out)?;
            flatten_expr(expr_type, out)?;
            flatten_expr(field_type, out)?;
        }

        // ════════════════════════════════════════════════════════════════════════
        // Cubical mode certificates
        // ════════════════════════════════════════════════════════════════════════
        ProofCert::CubicalInterval => {
            out.push(Fr::from(tags::CUBICAL_INTERVAL));
        }

        ProofCert::CubicalEndpoint { is_one } => {
            out.push(Fr::from(tags::CUBICAL_ENDPOINT));
            out.push(Fr::from(if *is_one { 1u64 } else { 0u64 }));
        }

        ProofCert::CubicalPath {
            ty_cert,
            ty_level,
            left_cert,
            right_cert,
        } => {
            out.push(Fr::from(tags::CUBICAL_PATH));
            flatten_cert(ty_cert, out)?;
            flatten_level(ty_level, out);
            flatten_cert(left_cert, out)?;
            flatten_cert(right_cert, out)?;
        }

        ProofCert::CubicalPathLam {
            body_cert,
            body_type,
            result_type,
        } => {
            out.push(Fr::from(tags::CUBICAL_PATH_LAM));
            flatten_cert(body_cert, out)?;
            flatten_expr(body_type, out)?;
            flatten_expr(result_type, out)?;
        }

        ProofCert::CubicalPathApp {
            path_cert,
            arg_cert,
            path_type,
            result_type,
        } => {
            out.push(Fr::from(tags::CUBICAL_PATH_APP));
            flatten_cert(path_cert, out)?;
            flatten_cert(arg_cert, out)?;
            flatten_expr(path_type, out)?;
            flatten_expr(result_type, out)?;
        }

        ProofCert::CubicalHComp {
            ty_cert,
            phi_cert,
            u_cert,
            base_cert,
            result_type,
        } => {
            out.push(Fr::from(tags::CUBICAL_HCOMP));
            flatten_cert(ty_cert, out)?;
            flatten_cert(phi_cert, out)?;
            flatten_cert(u_cert, out)?;
            flatten_cert(base_cert, out)?;
            flatten_expr(result_type, out)?;
        }

        ProofCert::CubicalTransp {
            ty_cert,
            phi_cert,
            base_cert,
            result_type,
        } => {
            out.push(Fr::from(tags::CUBICAL_TRANSP));
            flatten_cert(ty_cert, out)?;
            flatten_cert(phi_cert, out)?;
            flatten_cert(base_cert, out)?;
            flatten_expr(result_type, out)?;
        }

        ProofCert::CubicalCoe {
            ty_cert,
            r_cert,
            s_cert,
            base_cert,
            result_type,
        } => {
            out.push(Fr::from(tags::CUBICAL_COE));
            flatten_cert(ty_cert, out)?;
            flatten_cert(r_cert, out)?;
            flatten_cert(s_cert, out)?;
            flatten_cert(base_cert, out)?;
            flatten_expr(result_type, out)?;
        }

        // ════════════════════════════════════════════════════════════════════════
        // ZFC/Set-theoretic mode certificates
        // ════════════════════════════════════════════════════════════════════════
        ProofCert::ZFCSet { kind, result_type } => {
            out.push(Fr::from(tags::ZFC_SET));
            flatten_zfc_set_kind(kind, out)?;
            flatten_expr(result_type, out)?;
        }

        ProofCert::ZFCMem {
            elem_cert,
            set_cert,
        } => {
            out.push(Fr::from(tags::ZFC_MEM));
            flatten_cert(elem_cert, out)?;
            flatten_cert(set_cert, out)?;
        }

        ProofCert::ZFCComprehension {
            var_ty_cert,
            pred_cert,
            result_type,
        } => {
            out.push(Fr::from(tags::ZFC_COMPREHENSION));
            flatten_cert(var_ty_cert, out)?;
            flatten_cert(pred_cert, out)?;
            flatten_expr(result_type, out)?;
        }

        // ════════════════════════════════════════════════════════════════════════
        // Impredicative mode certificates
        // ════════════════════════════════════════════════════════════════════════
        ProofCert::SProp => {
            out.push(Fr::from(tags::SPROP));
        }

        ProofCert::Squash { inner_cert } => {
            out.push(Fr::from(tags::SQUASH));
            flatten_cert(inner_cert, out)?;
        }
    }

    Ok(())
}

/// Flatten a ZFCSetCertKind to field elements
fn flatten_zfc_set_kind(kind: &ZFCSetCertKind, out: &mut Vec<Fr>) -> Result<(), CommitError> {
    match kind {
        ZFCSetCertKind::Empty => {
            out.push(Fr::from(tags::zfc::EMPTY));
        }
        ZFCSetCertKind::Singleton(cert) => {
            out.push(Fr::from(tags::zfc::SINGLETON));
            flatten_cert(cert, out)?;
        }
        ZFCSetCertKind::Pair(cert1, cert2) => {
            out.push(Fr::from(tags::zfc::PAIR));
            flatten_cert(cert1, out)?;
            flatten_cert(cert2, out)?;
        }
        ZFCSetCertKind::Union(cert) => {
            out.push(Fr::from(tags::zfc::UNION));
            flatten_cert(cert, out)?;
        }
        ZFCSetCertKind::PowerSet(cert) => {
            out.push(Fr::from(tags::zfc::POWERSET));
            flatten_cert(cert, out)?;
        }
        ZFCSetCertKind::Separation {
            set_cert,
            pred_cert,
        } => {
            out.push(Fr::from(tags::zfc::SEPARATION));
            flatten_cert(set_cert, out)?;
            flatten_cert(pred_cert, out)?;
        }
        ZFCSetCertKind::Replacement {
            set_cert,
            func_cert,
        } => {
            out.push(Fr::from(tags::zfc::REPLACEMENT));
            flatten_cert(set_cert, out)?;
            flatten_cert(func_cert, out)?;
        }
        ZFCSetCertKind::Infinity => {
            out.push(Fr::from(tags::zfc::INFINITY));
        }
        ZFCSetCertKind::Choice(cert) => {
            out.push(Fr::from(tags::zfc::CHOICE));
            flatten_cert(cert, out)?;
        }
    }
    Ok(())
}

/// Flatten a Level to field elements
fn flatten_level(level: &Level, out: &mut Vec<Fr>) {
    match level {
        Level::Zero => {
            out.push(Fr::from(0u64)); // Zero tag
        }
        Level::Succ(inner) => {
            out.push(Fr::from(1u64)); // Succ tag
            flatten_level(inner, out);
        }
        Level::Max(l1, l2) => {
            out.push(Fr::from(2u64)); // Max tag
            flatten_level(l1, out);
            flatten_level(l2, out);
        }
        Level::IMax(l1, l2) => {
            out.push(Fr::from(3u64)); // IMax tag
            flatten_level(l1, out);
            flatten_level(l2, out);
        }
        Level::Param(name) => {
            out.push(Fr::from(4u64)); // Param tag
            flatten_name(name, out);
        }
    }
}

/// Flatten a Name to field elements
fn flatten_name(name: &Name, out: &mut Vec<Fr>) {
    match name.inner() {
        NameInner::Anon => {
            out.push(Fr::from(0u64)); // Anon tag
        }
        NameInner::Str(parent, s) => {
            out.push(Fr::from(1u64)); // Str tag
            flatten_name(parent, out);
            // Hash string to field element
            let hash = hash_string(s);
            out.push(hash);
        }
        NameInner::Num(parent, n) => {
            out.push(Fr::from(2u64)); // Num tag
            flatten_name(parent, out);
            out.push(Fr::from(*n));
        }
    }
}

/// Flatten an Expr to field elements (simplified encoding)
fn flatten_expr(expr: &Expr, out: &mut Vec<Fr>) -> Result<(), CommitError> {
    // For now, use a simplified hash-based encoding of expressions
    // Full encoding would mirror the certificate encoding structure
    let hash = hash_expr(expr);
    out.push(hash);
    Ok(())
}

/// Hash a string to a field element
fn hash_string(s: &str) -> Fr {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut hasher = DefaultHasher::new();
    s.hash(&mut hasher);
    Fr::from(hasher.finish())
}

/// Hash an expression to a field element (simplified)
fn hash_expr(expr: &Expr) -> Fr {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut hasher = DefaultHasher::new();
    // Use debug representation for hashing (not ideal but functional)
    format!("{expr:?}").hash(&mut hasher);
    Fr::from(hasher.finish())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_poly::Polynomial;
    use clean_kernel::cert::ZFCSetCertKind;
    use clean_kernel::expr::{BinderInfo, FVarId};
    use clean_kernel::{BigNat, Literal};

    /// Helper to create a simple type expression (Sort 0)
    fn type0() -> Box<Expr> {
        Box::new(Expr::sort(Level::Zero))
    }

    #[test]
    fn test_encode_sort() {
        let cert = ProofCert::Sort { level: Level::Zero };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        assert!(encoded.poly.degree() < encoded.domain_size);
        assert!(encoded.element_count > 0);
    }

    #[test]
    fn test_encode_decode_roundtrip() {
        let cert = ProofCert::Sort {
            level: Level::succ(Level::Zero),
        };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        // First elements should match
        assert_eq!(decoded[0], Fr::from(tags::SORT));
    }

    #[test]
    fn test_encode_bvar() {
        let cert = ProofCert::BVar {
            idx: 0,
            expected_type: type0(),
        };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::BVAR));
        assert_eq!(decoded[1], Fr::from(0u64)); // idx
    }

    #[test]
    fn test_encode_fvar() {
        let cert = ProofCert::FVar {
            id: FVarId::new(42),
            type_: type0(),
        };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::FVAR));
        assert_eq!(decoded[1], Fr::from(42u64)); // FVarId value
    }

    #[test]
    fn test_encode_const() {
        let cert = ProofCert::Const {
            name: Name::anon(),
            levels: vec![Level::Zero],
            type_: type0(),
        };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::CONST));
    }

    #[test]
    fn test_encode_app() {
        let fn_cert = Box::new(ProofCert::Sort { level: Level::Zero });
        let arg_cert = Box::new(ProofCert::Sort { level: Level::Zero });

        let cert = ProofCert::App {
            fn_cert,
            fn_type: type0(),
            arg_cert,
            result_type: type0(),
        };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::APP));
    }

    #[test]
    fn test_encode_lam() {
        let arg_type_cert = Box::new(ProofCert::Sort { level: Level::Zero });
        let body_cert = Box::new(ProofCert::Sort { level: Level::Zero });

        let cert = ProofCert::Lam {
            binder_info: BinderInfo::Default,
            arg_type_cert,
            body_cert,
            result_type: type0(),
        };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::LAM));
        assert_eq!(decoded[1], Fr::from(BinderInfo::Default as u64));
    }

    #[test]
    fn test_encode_pi() {
        let arg_type_cert = Box::new(ProofCert::Sort { level: Level::Zero });
        let body_type_cert = Box::new(ProofCert::Sort { level: Level::Zero });

        let cert = ProofCert::Pi {
            binder_info: BinderInfo::Implicit,
            arg_type_cert,
            arg_level: Level::Zero,
            body_type_cert,
            body_level: Level::Zero,
        };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::PI));
        assert_eq!(decoded[1], Fr::from(BinderInfo::Implicit as u64));
    }

    #[test]
    fn test_encode_let() {
        let type_cert = Box::new(ProofCert::Sort { level: Level::Zero });
        let value_cert = Box::new(ProofCert::Sort { level: Level::Zero });
        let body_cert = Box::new(ProofCert::Sort { level: Level::Zero });

        let cert = ProofCert::Let {
            type_cert,
            value_cert,
            body_cert,
            result_type: type0(),
        };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::LET));
    }

    #[test]
    fn test_encode_lit_nat() {
        let cert = ProofCert::Lit {
            lit: Literal::Nat(BigNat::Small(12345)),
            type_: type0(),
        };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::LIT));
        assert_eq!(decoded[1], Fr::from(0u64)); // Nat tag
    }

    #[test]
    fn test_encode_lit_string() {
        let cert = ProofCert::Lit {
            lit: Literal::String("hello".into()),
            type_: type0(),
        };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::LIT));
        assert_eq!(decoded[1], Fr::from(1u64)); // String tag
    }

    #[test]
    fn test_encode_cubical_interval() {
        let cert = ProofCert::CubicalInterval;

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::CUBICAL_INTERVAL));
    }

    #[test]
    fn test_encode_cubical_endpoint() {
        let cert = ProofCert::CubicalEndpoint { is_one: true };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::CUBICAL_ENDPOINT));
        assert_eq!(decoded[1], Fr::from(1u64)); // is_one = true
    }

    #[test]
    fn test_encode_sprop() {
        let cert = ProofCert::SProp;

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::SPROP));
    }

    #[test]
    fn test_encode_squash() {
        let inner_cert = Box::new(ProofCert::Sort { level: Level::Zero });

        let cert = ProofCert::Squash { inner_cert };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::SQUASH));
    }

    #[test]
    fn test_encode_zfc_empty_set() {
        let cert = ProofCert::ZFCSet {
            kind: ZFCSetCertKind::Empty,
            result_type: type0(),
        };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::ZFC_SET));
        assert_eq!(decoded[1], Fr::from(tags::zfc::EMPTY));
    }

    #[test]
    fn test_encode_zfc_infinity() {
        let cert = ProofCert::ZFCSet {
            kind: ZFCSetCertKind::Infinity,
            result_type: type0(),
        };

        let encoded = encode_cert(&cert).expect("encoding should succeed");
        let decoded = decode_cert(&encoded);

        assert_eq!(decoded[0], Fr::from(tags::ZFC_SET));
        assert_eq!(decoded[1], Fr::from(tags::zfc::INFINITY));
    }

    #[test]
    fn test_flatten_level_variants() {
        // Test all Level variants encode correctly
        let levels = vec![
            Level::Zero,
            Level::succ(Level::Zero),
            Level::Max(Level::Zero.into(), Level::Zero.into()),
            Level::IMax(Level::Zero.into(), Level::Zero.into()),
            Level::Param(Name::anon()),
        ];

        for level in levels {
            let cert = ProofCert::Sort { level };
            let encoded = encode_cert(&cert).expect("encoding should succeed");
            assert!(encoded.element_count > 0);
        }
    }

    #[test]
    fn test_flatten_name_variants() {
        // Test different Name variants via Const encoding
        let names = vec![
            Name::anon(),
            Name::str(Name::anon(), "test"),
            Name::num(Name::anon(), 42),
            Name::str(Name::str(Name::anon(), "Lean"), "Core"),
        ];

        for name in names {
            let cert = ProofCert::Const {
                name,
                levels: vec![],
                type_: type0(),
            };
            let encoded = encode_cert(&cert).expect("encoding should succeed");
            assert!(encoded.element_count > 0);
        }
    }

    #[test]
    fn test_domain_size_power_of_two() {
        // Verify domain size is always a power of 2
        let certs = vec![
            ProofCert::Sort { level: Level::Zero },
            ProofCert::CubicalInterval,
            ProofCert::SProp,
        ];

        for cert in certs {
            let encoded = encode_cert(&cert).expect("encoding should succeed");
            assert!(encoded.domain_size.is_power_of_two());
            assert!(encoded.domain_size >= encoded.element_count);
        }
    }
}
