// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Canonical, resource-bounded legacy-bincode carrier for Clean kernel terms.
//!
//! Existing TrustIR/Clean TV and contract payloads use bincode 1.x's historical
//! helper-function wire format: little-endian fixed-width integers. This module
//! preserves those bytes while replacing the legacy decoder's unlimited and
//! trailing-byte-accepting behavior with one exact whole-slice contract.

use super::evidence::ProofDigest;
use bincode::Options;
use clean_kernel::env::{ConstantInfo, Declaration, Environment};
use clean_kernel::{
    ConstructorVal, DecodeResourceLimits, Expr, InductiveVal, Name, QuotVal, RecursorVal,
};

/// Maximum encoded size of one Clean kernel proof/comparand expression (64 MiB).
pub const CLEAN_EXPR_V1_MAX_BYTES: usize = 64 * 1024 * 1024;
/// Maximum aggregate Expr/Level/Name nodes decoded from one carrier.
pub const CLEAN_EXPR_V1_MAX_NODES: usize = 2_000_000;
/// Maximum recursive Expr/Level/Name depth decoded from one carrier.
pub const CLEAN_EXPR_V1_MAX_DEPTH: usize = 4_096;

fn codec(limit: usize) -> impl Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .reject_trailing_bytes()
        .with_limit(limit as u64)
}

/// Encode one kernel expression in the existing bincode-1-compatible wire
/// format, rejecting values whose encoded carrier exceeds the hard limit.
pub fn encode_clean_expr_v1(expr: &Expr) -> Result<Vec<u8>, String> {
    let bytes = codec(CLEAN_EXPR_V1_MAX_BYTES)
        .serialize(expr)
        .map_err(|error| format!("encode Clean Expr v1: {error}"))?;
    if bytes.len() > CLEAN_EXPR_V1_MAX_BYTES {
        return Err(format!(
            "Clean Expr v1 carrier is {} bytes, exceeds limit {}",
            bytes.len(),
            CLEAN_EXPR_V1_MAX_BYTES
        ));
    }
    Ok(bytes)
}

/// Decode one untrusted kernel expression with exact whole-slice, byte, node,
/// depth, and canonical-reencoding checks.
pub fn decode_clean_expr_v1(bytes: &[u8]) -> Result<Expr, String> {
    decode_with_limits(
        bytes,
        CLEAN_EXPR_V1_MAX_BYTES,
        CLEAN_EXPR_V1_MAX_NODES,
        CLEAN_EXPR_V1_MAX_DEPTH,
    )
}

fn decode_with_limits(
    bytes: &[u8],
    max_bytes: usize,
    max_nodes: usize,
    max_depth: usize,
) -> Result<Expr, String> {
    if bytes.len() > max_bytes {
        return Err(format!(
            "Clean Expr v1 carrier is {} bytes, exceeds limit {max_bytes}",
            bytes.len()
        ));
    }
    let expr = clean_kernel::with_decode_resource_limits(
        DecodeResourceLimits {
            max_nodes,
            max_depth,
        },
        || codec(max_bytes).deserialize::<Expr>(bytes),
    )
    .map_err(|error| format!("decode Clean Expr v1: {error}"))?;

    // `reject_trailing_bytes` establishes whole-slice consumption. Re-encoding
    // additionally pins one canonical spelling and catches future serde codecs
    // that accept alternate structural representations.
    let canonical = codec(max_bytes)
        .serialize(&expr)
        .map_err(|error| format!("re-encode Clean Expr v1: {error}"))?;
    if canonical != bytes {
        return Err(format!(
            "non-canonical Clean Expr v1 carrier: supplied {} bytes, canonical encoding is {} bytes",
            bytes.len(),
            canonical.len()
        ));
    }
    Ok(expr)
}

/// Maximum encoded size of one island declaration closure (64 MiB) — the
/// same byte ceiling as one [`encode_clean_expr_v1`] carrier.
pub const ISLAND_DECLARATIONS_V1_MAX_BYTES: usize = 64 * 1024 * 1024;
/// Maximum number of declarations one island may carry.
pub const ISLAND_DECLARATIONS_V1_MAX_DECLARATIONS: usize = 4_096;
/// Maximum aggregate Expr/Level/Name nodes decoded from one island (the
/// budget spans EVERY declaration: an island is one carrier, not many).
pub const ISLAND_DECLARATIONS_V1_MAX_NODES: usize = 4_000_000;
/// Maximum recursive Expr/Level/Name depth decoded from one island.
pub const ISLAND_DECLARATIONS_V1_MAX_DEPTH: usize = CLEAN_EXPR_V1_MAX_DEPTH;

/// Encode an island's declaration closure (roadmap WS1.13) in the canonical
/// bincode-1-compatible carrier [`decode_island_declarations_v1`] reads — the
/// bytes an [`IslandEnvironment::declarations`] holds, in the order the
/// validator will insert them (a declaration may cite only the anchor
/// environment and the declarations BEFORE it).
///
/// [`IslandEnvironment::declarations`]: crate::proof::IslandEnvironment::declarations
pub fn encode_island_declarations_v1(declarations: &[Declaration]) -> Result<Vec<u8>, String> {
    if declarations.len() > ISLAND_DECLARATIONS_V1_MAX_DECLARATIONS {
        return Err(format!(
            "island carries {} declarations, exceeds limit {ISLAND_DECLARATIONS_V1_MAX_DECLARATIONS}",
            declarations.len()
        ));
    }
    let bytes = codec(ISLAND_DECLARATIONS_V1_MAX_BYTES)
        .serialize(declarations)
        .map_err(|error| format!("encode island declarations v1: {error}"))?;
    if bytes.len() > ISLAND_DECLARATIONS_V1_MAX_BYTES {
        return Err(format!(
            "island declarations v1 carrier is {} bytes, exceeds limit \
             {ISLAND_DECLARATIONS_V1_MAX_BYTES}",
            bytes.len()
        ));
    }
    Ok(bytes)
}

/// Decode an UNTRUSTED island declaration closure with the same exact
/// whole-slice, byte, node, depth and canonical-re-encoding checks as
/// [`decode_clean_expr_v1`], plus a declaration-count ceiling. This is the
/// anchor's own bounded decoder (`docs/SPEC_RATIFICATIONS.md` §8): nothing
/// else in trust-ir reads the bytes, and a decoded declaration is still
/// nothing until the Clean kernel accepts it on insertion.
pub fn decode_island_declarations_v1(bytes: &[u8]) -> Result<Vec<Declaration>, String> {
    decode_island_with_limits(
        bytes,
        ISLAND_DECLARATIONS_V1_MAX_BYTES,
        ISLAND_DECLARATIONS_V1_MAX_NODES,
        ISLAND_DECLARATIONS_V1_MAX_DEPTH,
        ISLAND_DECLARATIONS_V1_MAX_DECLARATIONS,
    )
}

fn decode_island_with_limits(
    bytes: &[u8],
    max_bytes: usize,
    max_nodes: usize,
    max_depth: usize,
    max_declarations: usize,
) -> Result<Vec<Declaration>, String> {
    if bytes.len() > max_bytes {
        return Err(format!(
            "island declarations v1 carrier is {} bytes, exceeds limit {max_bytes}",
            bytes.len()
        ));
    }
    let declarations = clean_kernel::with_decode_resource_limits(
        DecodeResourceLimits {
            max_nodes,
            max_depth,
        },
        || codec(max_bytes).deserialize::<Vec<Declaration>>(bytes),
    )
    .map_err(|error| format!("decode island declarations v1: {error}"))?;
    if declarations.len() > max_declarations {
        return Err(format!(
            "island carries {} declarations, exceeds limit {max_declarations}",
            declarations.len()
        ));
    }
    let canonical = codec(max_bytes)
        .serialize(&declarations)
        .map_err(|error| format!("re-encode island declarations v1: {error}"))?;
    if canonical != bytes {
        return Err(format!(
            "non-canonical island declarations v1 carrier: supplied {} bytes, canonical \
             encoding is {} bytes",
            bytes.len(),
            canonical.len()
        ));
    }
    Ok(declarations)
}

/// Digest domain of [`clean_cic_statement_digest`].
pub const CLEAN_CIC_STATEMENT_DIGEST_V1_DOMAIN: &str = "trust_ir.clean_cic.statement.v1";

/// Digest domain of [`kernel_environment_digest`].
pub const KERNEL_ENVIRONMENT_DIGEST_V1_DOMAIN: &str = "trust_ir.clean_cic.environment.v1";

/// The identity of a kernel STATEMENT — [`CertificateBinding::statement_digest`]
/// (roadmap WS1.12a): SHA-256 under `trust_ir.clean_cic.statement.v1` over
/// the statement's canonical v1 carrier ([`encode_clean_expr_v1`]).
///
/// A validator computes it over the statement IT derives (the backend-TV
/// `∀`-equation, the grounded contract goal) and compares it with what the
/// certificate claims; the producer never chooses the statement, so a
/// mismatch is a refusal. Fails only when the statement does not fit the
/// carrier, which the same validator would refuse anyway.
///
/// [`CertificateBinding::statement_digest`]: crate::proof::CertificateBinding::statement_digest
pub fn clean_cic_statement_digest(statement: &Expr) -> Result<ProofDigest, String> {
    let bytes = encode_clean_expr_v1(statement)?;
    Ok(ProofDigest::sha256_domain(
        CLEAN_CIC_STATEMENT_DIGEST_V1_DOMAIN,
        &bytes,
    ))
}

/// The CONTENT identity of a kernel environment —
/// [`CertificateBinding::environment_digest`] (roadmap WS1.12a; finding
/// F-007): SHA-256 under `trust_ir.clean_cic.environment.v1` over every
/// declaration the environment holds, in a canonical order that does not
/// depend on insertion order or hashing.
///
/// The preimage is: the [`CleanMode`] name; then the constants, inductives,
/// constructors, recursors and quotient primitives, each table sorted by
/// name, each entry spelled with every field that bears on a kernel judgment
/// — names, universe parameters, kind, reducibility, the type (and value
/// where one exists) as v1 carriers, and the structural counts and flags of
/// the inductive family. A lazily-backed environment is refused: its constants
/// are not enumerable, so its identity cannot be stated.
///
/// This is computed by trust-ir over the pinned `clean-kernel`'s public
/// iteration API, not by the kernel itself: the kernel exposes no canonical
/// environment digest (measured at the pinned rev), and a digest defined here
/// is what both the minter and the re-checker run, so they agree by
/// construction. What it establishes: a certificate re-checks only in an
/// environment whose DECLARATIONS equal the minting one's. What it does not:
/// the kernel's own type-checking code is not in the preimage (that is the
/// build identity, WS8.4).
///
/// [`CertificateBinding::environment_digest`]: crate::proof::CertificateBinding::environment_digest
/// [`CleanMode`]: clean_kernel::CleanMode
pub fn kernel_environment_digest(env: &Environment) -> Result<ProofDigest, String> {
    use super::evidence::{write_len_stable, write_str_stable, write_u8_stable, write_u32_stable};
    fn names(out: &mut Vec<u8>, names: &[Name]) {
        write_len_stable(out, names.len());
        for name in names {
            write_str_stable(out, &name.to_string());
        }
    }
    fn expr(out: &mut Vec<u8>, e: &Expr) -> Result<(), String> {
        let bytes = encode_clean_expr_v1(e)?;
        write_len_stable(out, bytes.len());
        out.extend_from_slice(&bytes);
        Ok(())
    }
    fn debug_tag(out: &mut Vec<u8>, value: &dyn core::fmt::Debug) {
        write_str_stable(out, &format!("{value:?}"));
    }
    if env.has_constant_source() {
        return Err(
            "kernel environment is lazily backed: its declarations are not enumerable, so its \
             identity cannot be stated"
                .to_string(),
        );
    }
    let mut out = Vec::new();
    debug_tag(&mut out, &env.mode());

    let mut constants: Vec<&ConstantInfo> = env.constants().collect();
    constants.sort_by_key(|c| c.name.to_string());
    write_len_stable(&mut out, constants.len());
    for c in constants {
        write_str_stable(&mut out, &c.name.to_string());
        names(&mut out, &c.level_params);
        debug_tag(&mut out, &c.kind);
        write_u8_stable(&mut out, u8::from(c.is_reducible));
        debug_tag(&mut out, &c.reducibility);
        expr(&mut out, &c.type_)?;
        match &c.value {
            None => write_u8_stable(&mut out, 0),
            Some(value) => {
                write_u8_stable(&mut out, 1);
                expr(&mut out, value)?;
            }
        }
    }

    let mut inductives: Vec<&InductiveVal> = env.inductives().collect();
    inductives.sort_by_key(|i| i.name.to_string());
    write_len_stable(&mut out, inductives.len());
    for i in inductives {
        write_str_stable(&mut out, &i.name.to_string());
        names(&mut out, &i.level_params);
        expr(&mut out, &i.type_)?;
        write_u32_stable(&mut out, i.num_params);
        write_u32_stable(&mut out, i.num_indices);
        names(&mut out, &i.all_names);
        names(&mut out, &i.constructor_names);
        for flag in [i.is_recursive, i.is_reflexive, i.is_large_elim, i.is_nested] {
            write_u8_stable(&mut out, u8::from(flag));
        }
    }

    let mut constructors: Vec<&ConstructorVal> = env.constructors().collect();
    constructors.sort_by_key(|c| c.name.to_string());
    write_len_stable(&mut out, constructors.len());
    for c in constructors {
        write_str_stable(&mut out, &c.name.to_string());
        write_str_stable(&mut out, &c.inductive_name.to_string());
        names(&mut out, &c.level_params);
        expr(&mut out, &c.type_)?;
        write_u32_stable(&mut out, c.num_params);
        write_u32_stable(&mut out, c.num_fields);
        write_u32_stable(&mut out, c.constructor_idx);
    }

    let mut recursors: Vec<&RecursorVal> = env.recursors().collect();
    recursors.sort_by_key(|r| r.name.to_string());
    write_len_stable(&mut out, recursors.len());
    for r in recursors {
        write_str_stable(&mut out, &r.name.to_string());
        debug_tag(&mut out, &r.arg_order);
        names(&mut out, &r.level_params);
        expr(&mut out, &r.type_)?;
        write_str_stable(&mut out, &r.inductive_name.to_string());
        for count in [r.num_params, r.num_indices, r.num_motives, r.num_minors] {
            write_u32_stable(&mut out, count);
        }
        write_len_stable(&mut out, r.rules.len());
        for rule in &r.rules {
            write_str_stable(&mut out, &rule.constructor_name.to_string());
            write_u32_stable(&mut out, rule.num_fields);
            write_len_stable(&mut out, rule.recursive_fields.len());
            for recursive in &rule.recursive_fields {
                write_u8_stable(&mut out, u8::from(*recursive));
            }
            expr(&mut out, &rule.rhs)?;
        }
        write_u8_stable(&mut out, u8::from(r.is_k));
    }

    let mut quotients: Vec<&QuotVal> = env.quotients().collect();
    quotients.sort_by_key(|q| q.name.to_string());
    write_len_stable(&mut out, quotients.len());
    for q in quotients {
        write_str_stable(&mut out, &q.name.to_string());
        names(&mut out, &q.level_params);
        expr(&mut out, &q.type_)?;
        debug_tag(&mut out, &q.kind);
    }

    Ok(ProofDigest::sha256_domain(
        KERNEL_ENVIRONMENT_DIGEST_V1_DOMAIN,
        &out,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn statement_digest_is_domain_separated_and_content_bound() {
        let a = clean_cic_statement_digest(&Expr::const_str("Bool.true")).unwrap();
        let b = clean_cic_statement_digest(&Expr::const_str("Bool.false")).unwrap();
        assert_ne!(a, b);
        let raw = ProofDigest::sha256(
            <sha2::Sha256 as sha2::Digest>::digest(
                encode_clean_expr_v1(&Expr::const_str("Bool.true")).unwrap(),
            )
            .into(),
        );
        assert_ne!(a, raw, "the domain separates the digest from a bare hash");
    }

    #[test]
    fn environment_digest_is_deterministic_and_sees_every_declaration() {
        let base = Environment::with_prelude();
        let d1 = kernel_environment_digest(&base).unwrap();
        let d2 = kernel_environment_digest(&Environment::with_prelude()).unwrap();
        assert_eq!(d1, d2, "two builds of the prelude have one identity");
        let mut extended = base.clone();
        extended
            .add_decl(clean_kernel::env::Declaration::Definition {
                name: Name::from_string("WS1_12.probe"),
                level_params: vec![],
                type_: Expr::const_str("Nat"),
                value: Expr::nat_lit(7),
                is_reducible: true,
            })
            .expect("a closed Nat definition is admitted");
        let d3 = kernel_environment_digest(&extended).unwrap();
        assert_ne!(
            d1, d3,
            "one added definition changes the environment identity"
        );
    }

    #[test]
    fn encoding_is_byte_compatible_with_legacy_bincode_helpers() {
        let expr = Expr::app(Expr::const_str("f"), Expr::nat_lit(7));
        assert_eq!(
            encode_clean_expr_v1(&expr).unwrap(),
            bincode::serialize(&expr).unwrap(),
            "hardening must not change the existing bincode-1 wire bytes"
        );
    }

    #[test]
    fn exact_decode_rejects_suffix_and_byte_overrun() {
        let bytes = encode_clean_expr_v1(&Expr::const_str("Bool.true")).unwrap();
        let mut suffixed = bytes.clone();
        suffixed.push(0);
        assert!(decode_clean_expr_v1(&suffixed).is_err());
        assert!(
            decode_with_limits(&bytes, bytes.len().saturating_sub(1), 100, 100).is_err(),
            "an encoded term over the configured byte cap must reject"
        );
    }

    fn island() -> Vec<Declaration> {
        vec![
            Declaration::Definition {
                name: Name::from_string("WS1_13.seven"),
                level_params: vec![],
                type_: Expr::const_str("Nat"),
                value: Expr::nat_lit(7),
                is_reducible: true,
            },
            Declaration::Theorem {
                name: Name::from_string("WS1_13.seven_eq"),
                level_params: vec![],
                type_: Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq"),
                        vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
                    ),
                    [
                        Expr::const_str("Nat"),
                        Expr::const_str("WS1_13.seven"),
                        Expr::nat_lit(7),
                    ],
                ),
                value: Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
                    ),
                    [Expr::const_str("Nat"), Expr::nat_lit(7)],
                ),
            },
        ]
    }

    #[test]
    fn island_declarations_round_trip_canonically() {
        let bytes = encode_island_declarations_v1(&island()).unwrap();
        let back = decode_island_declarations_v1(&bytes).unwrap();
        assert_eq!(back.len(), 2);
        assert_eq!(
            encode_island_declarations_v1(&back).unwrap(),
            bytes,
            "decode then encode is the identity on a canonical carrier"
        );
    }

    #[test]
    fn island_decode_rejects_suffix_overrun_and_too_many_declarations() {
        let bytes = encode_island_declarations_v1(&island()).unwrap();
        let mut suffixed = bytes.clone();
        suffixed.push(0);
        assert!(decode_island_declarations_v1(&suffixed).is_err());
        assert!(
            decode_island_with_limits(&bytes, bytes.len() - 1, 10_000, 100, 10).is_err(),
            "an island over the byte cap must reject"
        );
        let error = decode_island_with_limits(&bytes, bytes.len(), 10_000, 100, 1)
            .expect_err("two declarations over a one-declaration cap");
        assert!(error.contains("declarations"), "{error}");
        let error = decode_island_with_limits(&bytes, bytes.len(), 3, 100, 10)
            .expect_err("the node budget spans the whole island");
        assert!(error.contains("node"), "{error}");
    }

    #[test]
    fn exact_decode_rejects_excessive_recursive_depth() {
        let mut expr = Expr::nat_lit(0);
        for _ in 0..16 {
            expr = Expr::app(Expr::const_str("f"), expr);
        }
        let bytes = encode_clean_expr_v1(&expr).unwrap();
        let error = decode_with_limits(&bytes, bytes.len(), 10_000, 8)
            .expect_err("deep expression must fail inside the scoped decoder");
        assert!(error.contains("depth"), "unexpected error: {error}");
    }
}
