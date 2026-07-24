// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for advanced mathematical structures
//!
//! This module tests:
//! - Linear algebra (modules, vector spaces, linear maps, matrices)
//! - Category theory (categories, functors, natural transformations, adjunctions)
//! - Homological algebra (chain complexes, homology, derived categories)
//! - Number theory (primes, algebraic number theory, Galois theory)
//! - Algebraic geometry (varieties, schemes, sheaves)
//! - Representation theory (Lie groups, algebras, symmetric groups)
//! - Measure theory (measures, probability, integration)
//! - Functional analysis (Banach/Hilbert spaces, operators)
//! - Differential equations (ODEs, PDEs, dynamical systems)
//! - Combinatorics (graphs, matroids, enumeration)
//! - Optimization (convex, variational calculus, operations research)
//! - Computability (Turing machines, decidability, complexity theory)

use crate::env::test_helpers::assert_const;
use crate::env::*;

#[test]
fn test_cryptography_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_cryptography());
    env.init_cryptography().unwrap();
    assert!(env.has_cryptography());
}

#[test]
fn test_cryptography_idempotent() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();
    env.init_cryptography().unwrap();
    assert!(env.has_cryptography());
}

#[test]
fn test_cryptography_hardness_assumptions_exist() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();

    let hardness_names = [
        "Cryptography.OneWayFunction",
        "Cryptography.TrapdoorFunction",
        "Cryptography.PseudorandomGenerator",
        "Cryptography.PseudorandomFunction",
        "Cryptography.FactoringAssumption",
        "Cryptography.RSAAssumption",
        "Cryptography.DiscreteLogAssumption",
        "Cryptography.CDH",
        "Cryptography.DDH",
        "Cryptography.ECDLP",
        "Cryptography.LWE",
        "Cryptography.RingLWE",
        "Cryptography.SIS",
    ];

    for name in &hardness_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_cryptography_symmetric_exist() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();

    let sym_names = [
        "Cryptography.SymmetricEncryption",
        "Cryptography.BlockCipher",
        "Cryptography.AES",
        "Cryptography.ChaCha20",
        "Cryptography.CBCMode",
        "Cryptography.CTRMode",
        "Cryptography.GCMMode",
        "Cryptography.INDCPA",
        "Cryptography.INDCCA2",
        "Cryptography.AEAD",
    ];

    for name in &sym_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_cryptography_asymmetric_exist() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();

    let asym_names = [
        "Cryptography.PublicKeyEncryption",
        "Cryptography.RSAEncryption",
        "Cryptography.RSAOAEP",
        "Cryptography.ElGamal",
        "Cryptography.ECIES",
        "Cryptography.Kyber",
        "Cryptography.ClassicMcEliece",
    ];

    for name in &asym_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_cryptography_signatures_exist() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();

    let sig_names = [
        "Cryptography.DigitalSignature",
        "Cryptography.RSASignature",
        "Cryptography.ECDSA",
        "Cryptography.EdDSA",
        "Cryptography.Ed25519",
        "Cryptography.Schnorr",
        "Cryptography.BLS",
        "Cryptography.Dilithium",
        "Cryptography.SPHINCS",
        "Cryptography.EUFCMA",
    ];

    for name in &sig_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_cryptography_hash_functions_exist() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();

    let hash_names = [
        "Cryptography.HashFunction",
        "Cryptography.CollisionResistance",
        "Cryptography.PreimageResistance",
        "Cryptography.SHA256",
        "Cryptography.SHA3",
        "Cryptography.BLAKE3",
        "Cryptography.RandomOracle",
        "Cryptography.Argon2",
    ];

    for name in &hash_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_cryptography_macs_exist() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();

    let mac_names = [
        "Cryptography.MAC",
        "Cryptography.HMAC",
        "Cryptography.Poly1305",
        "Cryptography.MACUnforgeability",
    ];

    for name in &mac_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_cryptography_key_exchange_exist() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();

    let kex_names = [
        "Cryptography.KeyExchange",
        "Cryptography.DiffieHellman",
        "Cryptography.ECDH",
        "Cryptography.X25519",
        "Cryptography.TLS13",
        "Cryptography.PerfectForwardSecrecy",
    ];

    for name in &kex_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_cryptography_zk_exist() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();

    let zk_names = [
        "Cryptography.ZeroKnowledge",
        "Cryptography.Soundness",
        "Cryptography.ProofOfKnowledge",
        "Cryptography.SigmaProtocol",
        "Cryptography.FiatShamir",
        "Cryptography.SNARK",
        "Cryptography.STARK",
        "Cryptography.Groth16",
        "Cryptography.PLONK",
        "Cryptography.Bulletproofs",
    ];

    for name in &zk_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_cryptography_mpc_exist() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();

    let mpc_names = [
        "Cryptography.SecretSharing",
        "Cryptography.ShamirSecretSharing",
        "Cryptography.MPC",
        "Cryptography.GarbledCircuit",
        "Cryptography.OT",
    ];

    for name in &mpc_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_cryptography_fhe_exist() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();

    let fhe_names = [
        "Cryptography.HomomorphicEncryption",
        "Cryptography.FullyHomomorphic",
        "Cryptography.Bootstrapping",
        "Cryptography.BGV",
        "Cryptography.BFV",
        "Cryptography.CKKS",
        "Cryptography.TFHE",
    ];

    for name in &fhe_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_cryptography_commitments_exist() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();

    let commit_names = [
        "Cryptography.Commitment",
        "Cryptography.PedersenCommitment",
        "Cryptography.MerkleTree",
        "Cryptography.VectorCommitment",
    ];

    for name in &commit_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_cryptography_security_properties_exist() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();

    let sec_names = [
        "Cryptography.SemanticSecurity",
        "Cryptography.UCFramework",
        "Cryptography.GameBasedSecurity",
        "Cryptography.ReductionProof",
        "Cryptography.NegligibleFunction",
        "Cryptography.PPTAdversary",
    ];

    for name in &sec_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_cryptography_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_cryptography().unwrap();
    // Cryptography depends on number_theory and computability
    assert!(env.has_number_theory());
    assert!(env.has_computability());
}

#[test]
fn test_cryptography_key_types_well_formed() {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_cryptography().unwrap();
    let tc = TypeChecker::new(&env);

    for name in &[
        "Cryptography.SymmetricEncryption",
        "Cryptography.PublicKeyEncryption",
        "Cryptography.HashFunction",
        "Cryptography.DigitalSignature",
    ] {
        let expr = Expr::const_(Name::from_string(name), vec![Level::zero()]);
        let ty = tc
            .infer_type(&expr)
            .unwrap_or_else(|e| panic!("{name}: tc.infer_type failed: {e}"));
        assert!(
            matches!(&ty.kind, ExprKind::Sort(_) | ExprKind::Pi(..)),
            "{name}: expected Sort or Pi type, got {ty:?}"
        );
    }
}

// ============================================================================
// Real and Complex Analysis Tests
// ============================================================================
