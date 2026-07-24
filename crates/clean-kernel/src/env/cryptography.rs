// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cryptography structures for Environment
//!
//! This module contains axioms for cryptographic primitives and protocols:
//! - One-way functions and hardness assumptions
//! - Symmetric and asymmetric encryption
//! - Digital signatures and MACs
//! - Hash functions and random oracles
//! - Key exchange protocols
//! - Zero-knowledge proofs

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Cryptography module
    ///
    /// Cryptography provides the foundation for secure communication and
    /// authenticated computation. This module covers:
    /// - Hardness assumptions (discrete log, factoring, lattices)
    /// - Symmetric primitives (block ciphers, stream ciphers, MACs)
    /// - Asymmetric primitives (RSA, Diffie-Hellman, elliptic curves)
    /// - Hash functions and their security properties
    /// - Signature schemes and their unforgeability
    /// - Zero-knowledge proofs and their properties
    /// - Protocol security (CPA, CCA, IND, etc.)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.cryptography_init == true`
    /// ENSURES: On success, required dependencies (`eq`, `nat`, `number_theory`, `computability`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_cryptography(&mut self) -> Result<(), EnvError> {
        if self.cryptography_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_number_theory()?;
        self.init_computability()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Cryptography constants
        for name in &[
            // ================================================================
            // Hardness Assumptions
            // ================================================================
            "Cryptography.OneWayFunction",      // f : X → Y is one-way
            "Cryptography.TrapdoorFunction",    // one-way with trapdoor
            "Cryptography.TrapdoorPermutation", // trapdoor permutation
            "Cryptography.PseudorandomGenerator", // PRG stretches randomness
            "Cryptography.PseudorandomFunction", // PRF indistinguishable from random
            "Cryptography.PseudorandomPermutation", // PRP (block cipher model)
            // Factoring-based
            "Cryptography.FactoringAssumption", // hard to factor N=pq
            "Cryptography.RSAAssumption",       // hard to compute x from x^e mod N
            "Cryptography.StrongRSA",           // hard to find any e-th root
            "Cryptography.QuadraticResidueAssumption", // QR assumption
            // Discrete log-based
            "Cryptography.DiscreteLogAssumption", // hard to find x from g^x
            "Cryptography.CDH",                   // computational Diffie-Hellman
            "Cryptography.DDH",                   // decisional Diffie-Hellman
            "Cryptography.GapDH",                 // gap Diffie-Hellman
            "Cryptography.BCDH",                  // bilinear CDH
            "Cryptography.DBDH",                  // decisional bilinear DH
            // Elliptic curve-based
            "Cryptography.ECDLP",             // EC discrete log problem
            "Cryptography.ECCDH",             // EC computational DH
            "Cryptography.ECDDH",             // EC decisional DH
            "Cryptography.BilinearPairing",   // e: G1 × G2 → GT
            "Cryptography.PairingProperties", // bilinearity, non-degeneracy
            // Lattice-based
            "Cryptography.SVP",       // shortest vector problem
            "Cryptography.CVP",       // closest vector problem
            "Cryptography.LWE",       // learning with errors
            "Cryptography.RingLWE",   // ring-LWE
            "Cryptography.ModuleLWE", // module-LWE
            "Cryptography.SIS",       // short integer solution
            "Cryptography.NTRU",      // NTRU assumption
            // Code-based
            "Cryptography.SyndromeDecoding", // syndrome decoding problem
            "Cryptography.McElieceAssumption", // McEliece hardness
            // Multivariate
            "Cryptography.MQAssumption", // multivariate quadratic
            // ================================================================
            // Symmetric Encryption
            // ================================================================
            "Cryptography.SymmetricEncryption", // (KeyGen, Enc, Dec)
            "Cryptography.BlockCipher",         // E: K × M → C
            "Cryptography.StreamCipher",        // keystream generator
            "Cryptography.FeistelNetwork",      // Feistel construction
            "Cryptography.SPNetwork",           // substitution-permutation network
            "Cryptography.AES",                 // AES block cipher
            "Cryptography.AESKeySchedule",      // AES key expansion
            "Cryptography.AESSBox",             // AES substitution box
            "Cryptography.ChaCha20",            // ChaCha20 stream cipher
            "Cryptography.Salsa20",             // Salsa20 stream cipher
            // Modes of operation
            "Cryptography.ECBMode", // electronic codebook (insecure)
            "Cryptography.CBCMode", // cipher block chaining
            "Cryptography.CTRMode", // counter mode
            "Cryptography.GCMMode", // Galois/counter mode (AEAD)
            "Cryptography.CCMMode", // counter with CBC-MAC
            // Security notions
            "Cryptography.INDCPA",   // indistinguishability under CPA
            "Cryptography.INDCCA1",  // IND under CCA1 (lunchtime)
            "Cryptography.INDCCA2",  // IND under CCA2 (adaptive)
            "Cryptography.INTCTXT",  // integrity of ciphertexts
            "Cryptography.AEAD",     // authenticated encryption with AD
            "Cryptography.AESecure", // AE security definition
            // ================================================================
            // Asymmetric Encryption
            // ================================================================
            "Cryptography.PublicKeyEncryption", // (KeyGen, Enc, Dec)
            "Cryptography.RSAEncryption",       // textbook RSA
            "Cryptography.RSAOAEP",             // RSA with OAEP padding
            "Cryptography.ElGamal",             // ElGamal encryption
            "Cryptography.ECIES",               // EC integrated encryption
            "Cryptography.CramerShoup",         // Cramer-Shoup encryption
            "Cryptography.Paillier",            // Paillier homomorphic encryption
            // Post-quantum encryption
            "Cryptography.Kyber",           // NIST Kyber (ML-KEM)
            "Cryptography.Saber",           // Saber KEM
            "Cryptography.ClassicMcEliece", // McEliece encryption
            "Cryptography.NTRUPRIME",       // NTRU Prime encryption
            // ================================================================
            // Digital Signatures
            // ================================================================
            "Cryptography.DigitalSignature", // (KeyGen, Sign, Verify)
            "Cryptography.RSASignature",     // RSA-PSS signature
            "Cryptography.DSA",              // Digital Signature Algorithm
            "Cryptography.ECDSA",            // EC-DSA
            "Cryptography.EdDSA",            // Edwards-curve DSA
            "Cryptography.Ed25519",          // Ed25519 instantiation
            "Cryptography.Schnorr",          // Schnorr signature
            "Cryptography.BLS",              // Boneh-Lynn-Shacham signature
            "Cryptography.MultiSignature",   // multi-party signing
            "Cryptography.ThresholdSignature", // t-of-n threshold signing
            "Cryptography.BlindSignature",   // blind signatures
            "Cryptography.GroupSignature",   // group signatures
            "Cryptography.RingSignature",    // ring signatures
            // Post-quantum signatures
            "Cryptography.Dilithium", // NIST Dilithium (ML-DSA)
            "Cryptography.Falcon",    // FALCON signature
            "Cryptography.SPHINCS",   // SPHINCS+ hash-based
            // Security notions
            "Cryptography.EUFCMA", // existential unforgeability under CMA
            "Cryptography.SUFCMA", // strong unforgeability under CMA
            // ================================================================
            // Hash Functions
            // ================================================================
            "Cryptography.HashFunction",        // H: {0,1}* → {0,1}^n
            "Cryptography.CollisionResistance", // hard to find H(x)=H(y), x≠y
            "Cryptography.PreimageResistance",  // hard to find x from H(x)
            "Cryptography.SecondPreimageResistance", // hard to find y≠x, H(y)=H(x)
            "Cryptography.MerkleDamgard",       // Merkle-Damgård construction
            "Cryptography.SpongeConstruction",  // sponge construction (SHA-3)
            "Cryptography.SHA256",              // SHA-256 hash
            "Cryptography.SHA3",                // SHA-3 / Keccak
            "Cryptography.BLAKE2",              // BLAKE2 hash
            "Cryptography.BLAKE3",              // BLAKE3 hash
            // Random oracle model
            "Cryptography.RandomOracle",      // idealized hash function
            "Cryptography.RandomOracleModel", // ROM for proofs
            "Cryptography.StandardModel",     // proofs without ROM
            // Password hashing
            "Cryptography.PBKDF2", // password-based KDF
            "Cryptography.Bcrypt", // bcrypt password hash
            "Cryptography.Scrypt", // scrypt memory-hard
            "Cryptography.Argon2", // Argon2 winner of PHC
            // ================================================================
            // Message Authentication Codes
            // ================================================================
            "Cryptography.MAC",               // MAC: K × M → T
            "Cryptography.HMAC",              // HMAC construction
            "Cryptography.CBCMAC",            // CBC-MAC
            "Cryptography.CMAC",              // CMAC (OMAC)
            "Cryptography.Poly1305",          // Poly1305 MAC
            "Cryptography.GMAC",              // Galois MAC
            "Cryptography.MACUnforgeability", // unforgeability under CMA
            // ================================================================
            // Key Exchange
            // ================================================================
            "Cryptography.KeyExchange",   // key exchange protocol
            "Cryptography.DiffieHellman", // DH key exchange
            "Cryptography.ECDH",          // elliptic curve DH
            "Cryptography.X25519",        // Curve25519 key exchange
            "Cryptography.X448",          // Curve448 key exchange
            "Cryptography.MQV",           // authenticated MQV
            "Cryptography.HMQV",          // hashed MQV
            // Post-quantum key exchange
            "Cryptography.KEMEncapsulation", // KEM (KeyGen, Encaps, Decaps)
            "Cryptography.KEMINDCCA",        // KEM IND-CCA security
            // TLS/protocols
            "Cryptography.TLS12",                 // TLS 1.2 protocol
            "Cryptography.TLS13",                 // TLS 1.3 protocol
            "Cryptography.TLSHandshake",          // TLS handshake protocol
            "Cryptography.PerfectForwardSecrecy", // PFS property
            // ================================================================
            // Zero-Knowledge Proofs
            // ================================================================
            "Cryptography.ZeroKnowledge",      // zero-knowledge property
            "Cryptography.Soundness",          // soundness property
            "Cryptography.Completeness",       // completeness property
            "Cryptography.KnowledgeSoundness", // knowledge extraction
            "Cryptography.WitnessIndistinguishable", // witness indistinguishability
            "Cryptography.ProofOfKnowledge",   // proof of knowledge
            "Cryptography.SigmaProtocol",      // Sigma (3-round) protocol
            "Cryptography.FiatShamir",         // Fiat-Shamir transform
            "Cryptography.SchnorrProtocol",    // Schnorr identification
            "Cryptography.GrothSahai",         // Groth-Sahai proofs
            // SNARK/STARK
            "Cryptography.SNARK",                // succinct non-interactive ARK
            "Cryptography.STARK",                // scalable transparent ARK
            "Cryptography.Groth16",              // Groth16 SNARK
            "Cryptography.PLONK",                // PLONK proof system
            "Cryptography.Bulletproofs",         // Bulletproofs
            "Cryptography.PolynomialCommitment", // polynomial commitment scheme
            "Cryptography.KZGCommitment",        // Kate-Zaverucha-Goldberg
            "Cryptography.FRI",                  // fast Reed-Solomon IOP
            // ================================================================
            // Secret Sharing and MPC
            // ================================================================
            "Cryptography.SecretSharing",       // (t,n) secret sharing
            "Cryptography.ShamirSecretSharing", // Shamir's scheme
            "Cryptography.VSS",                 // verifiable secret sharing
            "Cryptography.PVSS",                // publicly verifiable SS
            "Cryptography.MPC",                 // secure multi-party computation
            "Cryptography.GarbledCircuit",      // Yao's garbled circuits
            "Cryptography.OT",                  // oblivious transfer
            "Cryptography.OTExtension",         // OT extension
            "Cryptography.GMW",                 // GMW protocol
            "Cryptography.BGW",                 // BGW protocol
            "Cryptography.SPDZ",                // SPDZ protocol
            // ================================================================
            // Homomorphic Encryption
            // ================================================================
            "Cryptography.HomomorphicEncryption", // HE definition
            "Cryptography.PartiallyHomomorphic",  // partial HE
            "Cryptography.SomewhatHomomorphic",   // somewhat HE
            "Cryptography.FullyHomomorphic",      // fully homomorphic encryption
            "Cryptography.Bootstrapping",         // FHE bootstrapping
            "Cryptography.BGV",                   // Brakerski-Gentry-Vaikuntanathan
            "Cryptography.BFV",                   // Brakerski-Fan-Vercauteren
            "Cryptography.CKKS",                  // Cheon-Kim-Kim-Song (approx)
            "Cryptography.TFHE",                  // torus FHE
            // ================================================================
            // Commitments
            // ================================================================
            "Cryptography.Commitment",               // commitment scheme
            "Cryptography.HidingCommitment",         // hiding property
            "Cryptography.BindingCommitment",        // binding property
            "Cryptography.PedersenCommitment",       // Pedersen commitment
            "Cryptography.HashCommitment",           // hash-based commitment
            "Cryptography.VectorCommitment",         // vector commitment
            "Cryptography.MerkleTree",               // Merkle tree commitment
            "Cryptography.AccumulatorCryptographic", // cryptographic accumulator
            // ================================================================
            // Blockchain / Consensus Crypto
            // ================================================================
            "Cryptography.VRF",                 // verifiable random function
            "Cryptography.VDF",                 // verifiable delay function
            "Cryptography.TimelockPuzzle",      // time-lock puzzle
            "Cryptography.ProofOfWork",         // proof of work (hash puzzle)
            "Cryptography.ProofOfStake",        // proof of stake primitive
            "Cryptography.BFTConsensus",        // BFT consensus primitive
            "Cryptography.ThresholdDecryption", // threshold decryption
            // ================================================================
            // Protocol Security Properties
            // ================================================================
            "Cryptography.SemanticSecurity", // semantic security
            "Cryptography.SimulationBasedSecurity", // simulation-based definition
            "Cryptography.UCFramework",      // universal composability
            "Cryptography.GameBasedSecurity", // game-based definition
            "Cryptography.ReductionProof",   // security reduction
            "Cryptography.TightnessOfReduction", // tightness of reduction
            "Cryptography.HybridArgument",   // hybrid argument technique
            "Cryptography.AdvantageDefinition", // advantage of adversary
            "Cryptography.NegligibleFunction", // negligible function
            "Cryptography.PPTAdversary",     // probabilistic poly-time adversary
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.cryptography_init = true;
        Ok(())
    }

    /// Check if Cryptography has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_cryptography` has completed successfully
    /// ENSURES: Pure - no side effects
    pub(crate) fn has_cryptography(&self) -> bool {
        self.cryptography_init
    }
}
