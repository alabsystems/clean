// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the kernel Declaration to `.mathverse` shard export pipeline.

use super::*;
use crate::shard::ShardReader;
use crate::types::{ContentDomain, ImportConfidence, SourceSystem};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::Name;

/// Build a simple theorem declaration: `thm : Prop := Prop`.
fn make_prop_theorem(name: &str) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::sort(Level::zero()), // Prop
        value: Expr::sort(Level::zero()), // Prop (not a valid proof, but fine for export)
    }
}

/// Build an axiom declaration: `ax : Prop`.
fn make_axiom(name: &str) -> Declaration {
    Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    }
}

/// Build a definition: `def : Nat -> Nat := fun x => x`.
fn make_definition(name: &str) -> Declaration {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let ty = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());
    let val = Expr::lam(BinderInfo::Default, nat, Expr::bvar(0));
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    }
}

#[test]
fn test_kernel_export_single_theorem() {
    let mut builder = KernelShardBuilder::new();
    let decl = make_prop_theorem("Test.myThm");
    let idx = builder.add_declaration(&decl, &["test", "prop"]).unwrap();
    assert_eq!(idx, 0);
    assert_eq!(builder.entry_count(), 1);

    let entry = &builder.entries()[0];
    assert_eq!(entry.name, "Test.myThm");
    assert!(entry.has_value);
    assert_eq!(entry.content_domain, ContentDomain::PureMath);
    assert_eq!(entry.tags, vec!["test", "prop"]);
}

#[test]
fn test_kernel_export_axiom_trust_level() {
    let mut builder = KernelShardBuilder::new();
    let decl = make_axiom("Classical.choice");
    builder.add_declaration(&decl, &[]).unwrap();

    let entry = &builder.entries()[0];
    assert!(!entry.has_value);
    assert!(entry.axiom_profile.has(AxiomProfile::AXIOMATIZED));
}

#[test]
fn test_kernel_export_nn_verification_domain() {
    let mut builder = KernelShardBuilder::new();
    let decl = make_prop_theorem("nn_verify.C001_robustness");
    builder
        .add_declaration(&decl, &["gamma-crown", "robustness"])
        .unwrap();

    let entry = &builder.entries()[0];
    assert_eq!(entry.content_domain, ContentDomain::NnVerification);
    assert!(entry.axiom_profile.has(AxiomProfile::FLOAT_APPROX));
    assert!(entry.axiom_profile.has(AxiomProfile::NN_ABSTRACTION));
}

#[test]
fn test_kernel_export_round_trip() {
    let mut builder = KernelShardBuilder::new();

    // Add multiple declarations of different kinds.
    let thm = make_prop_theorem("Test.theorem1");
    let ax = make_axiom("Test.axiom1");
    let def = make_definition("Test.identity");

    builder.add_declaration(&thm, &["theorem"]).unwrap();
    builder.add_declaration(&ax, &["axiom"]).unwrap();
    builder.add_declaration(&def, &["definition"]).unwrap();

    assert_eq!(builder.entry_count(), 3);

    // Write to bytes and read back.
    let bytes = builder.write_to_bytes().unwrap();
    let reader = ShardReader::from_bytes(&bytes).unwrap();

    // Verify constant count.
    assert_eq!(reader.header.constant_count, 3);

    // Verify name lookup works for all three.
    let (idx0, hdr0) = reader
        .lookup_name("Test.theorem1")
        .expect("theorem should be findable");
    assert_eq!(idx0, 0);
    assert_eq!(hdr0.source_system, SourceSystem::CleanNative as u8);
    assert_eq!(
        hdr0.import_confidence,
        ImportConfidence::KernelVerified as u8
    );
    assert!(hdr0.has_value());

    let (idx1, hdr1) = reader
        .lookup_name("Test.axiom1")
        .expect("axiom should be findable");
    assert_eq!(idx1, 1);
    assert_eq!(hdr1.import_confidence, ImportConfidence::Axiomatized as u8);
    assert!(!hdr1.has_value());
    assert!(hdr1.is_trust_gated()); // AXIOMATIZED bit is trust-gated

    let (idx2, hdr2) = reader
        .lookup_name("Test.identity")
        .expect("definition should be findable");
    assert_eq!(idx2, 2);
    assert!(hdr2.has_value());
    assert_eq!(hdr2.content_domain, ContentDomain::PureMath as u8);
}

/// REGRESSION (cake-gate FusedOracleMismatch on string-literal-bearing decls):
/// `clean_kernel::flat::FlatBuilder` keeps NAMES and string LITERALS in two
/// disjoint index spaces. The shard transfer must carry the literal table and
/// remap `Lit::String` through it — NOT through the name remap. A regression
/// here resolves every reconstructed string literal to an unrelated NAME (the
/// real bug: `Lit("")` reconstructed as `"Inhabited"`), so the round-trip oracle
/// rejects the (faithful) decl and blocks graduation. This pins the literal
/// payloads byte-for-byte across the shard round trip.
#[test]
fn test_kernel_export_string_literal_round_trips_faithfully() {
    // A value that mixes Const names with a string literal whose payload is
    // DISTINCT from every interned name, and is added AFTER names so a
    // name-table conflation would resolve it to the wrong slot.
    //   def Test.greeter : String := String.append "hello" "world"
    let string_ty = Expr::const_(Name::from_string("String"), vec![]);
    let append = Expr::const_(Name::from_string("String.append"), vec![]);
    let val = Expr::app(
        Expr::app(append, Expr::str_lit("hello")),
        Expr::str_lit("world"),
    );
    let decl = Declaration::Definition {
        name: Name::from_string("Test.greeter"),
        level_params: vec![],
        type_: string_ty,
        value: val,
        is_reducible: false,
    };

    let mut builder = KernelShardBuilder::new();
    builder.add_declaration(&decl, &[]).unwrap();
    let bytes = builder.write_to_bytes().unwrap();
    let reader = ShardReader::from_bytes(&bytes).unwrap();

    let (idx, hdr) = reader
        .lookup_name("Test.greeter")
        .expect("greeter should be findable");
    let recon_val = crate::shard_reconstruct::reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        hdr.value_idx,
    )
    .expect("value reconstructs");
    let _ = idx;

    // Collect the string literals from the reconstructed value, in app order.
    use clean_kernel::expr::{ExprKind, Literal};
    fn collect_str_lits(e: &Expr, out: &mut Vec<String>) {
        match e.kind() {
            ExprKind::Lit(Literal::String(s)) => out.push(s.to_string()),
            ExprKind::App(f, a) => {
                collect_str_lits(f, out);
                collect_str_lits(a, out);
            }
            _ => {}
        }
    }
    let mut lits = Vec::new();
    collect_str_lits(&recon_val, &mut lits);
    assert_eq!(
        lits,
        vec!["hello".to_string(), "world".to_string()],
        "string literals must survive the shard round trip with their exact \
         payloads (regression: literals resolved to NAME-table entries)"
    );
}

#[test]
fn test_kernel_export_file_round_trip() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("test_kernel.mathverse");

    let mut builder = KernelShardBuilder::new();
    builder
        .add_declaration(&make_prop_theorem("File.roundTrip"), &[])
        .unwrap();
    builder.write_to_file(&path).unwrap();

    let reader = ShardReader::from_file(&path).unwrap();
    assert_eq!(reader.header.constant_count, 1);
    assert!(reader.lookup_name("File.roundTrip").is_some());
}

#[test]
fn test_kernel_export_nn_shard_searchable() {
    let mut builder = KernelShardBuilder::new();

    // Simulate gamma-crown theorem exports.
    for i in 1..=5 {
        let name = format!("nn_verify.C{i:03}_robustness");
        let decl = make_prop_theorem(&name);
        builder
            .add_declaration(&decl, &["gamma-crown", "robustness"])
            .unwrap();
    }

    let bytes = builder.write_to_bytes().unwrap();
    let reader = ShardReader::from_bytes(&bytes).unwrap();

    assert_eq!(reader.header.constant_count, 5);

    // All should be findable by name.
    for i in 1..=5 {
        let name = format!("nn_verify.C{i:03}_robustness");
        let result = reader.lookup_name(&name);
        assert!(result.is_some(), "should find {name}");
        let (_, hdr) = result.unwrap();
        assert_eq!(hdr.content_domain, ContentDomain::NnVerification as u8);
        assert_eq!(hdr.source_system, SourceSystem::CleanNative as u8);
    }

    // Bloom filter should pass for all.
    for i in 1..=5 {
        let name = format!("nn_verify.C{i:03}_robustness");
        assert!(reader.bloom_maybe_contains(&name));
    }
}

#[test]
fn test_kernel_export_empty_shard() {
    let builder = KernelShardBuilder::new();
    assert_eq!(builder.entry_count(), 0);

    let bytes = builder.write_to_bytes().unwrap();
    let reader = ShardReader::from_bytes(&bytes).unwrap();
    assert_eq!(reader.header.constant_count, 0);
}

#[test]
fn test_kernel_export_definition_with_complex_type() {
    let mut builder = KernelShardBuilder::new();
    let def = make_definition("Complex.identity");
    let idx = builder.add_declaration(&def, &["complex"]).unwrap();
    assert_eq!(idx, 0);

    let entry = &builder.entries()[0];
    assert!(entry.has_value);
    assert_eq!(entry.axiom_profile, AxiomProfile::NONE);

    // Verify it round-trips.
    let bytes = builder.write_to_bytes().unwrap();
    let reader = ShardReader::from_bytes(&bytes).unwrap();
    let (_, hdr) = reader.lookup_name("Complex.identity").unwrap();
    assert!(hdr.has_value());
    assert_eq!(
        hdr.import_confidence,
        ImportConfidence::KernelVerified as u8
    );
}

#[test]
fn test_kernel_export_dedup_shared_subexprs() {
    // Two theorems with the same type (Prop) should share the Sort(0)
    // expression in the shard arena via hash-consing.
    let mut builder = KernelShardBuilder::new();
    builder
        .add_declaration(&make_prop_theorem("A"), &[])
        .unwrap();
    builder
        .add_declaration(&make_prop_theorem("B"), &[])
        .unwrap();

    let bytes = builder.write_to_bytes().unwrap();
    let reader = ShardReader::from_bytes(&bytes).unwrap();

    assert_eq!(reader.header.constant_count, 2);
    // Both constants should reference the same type expression (deduped).
    assert_eq!(
        reader.constants[0].type_idx, reader.constants[1].type_idx,
        "shared type expressions should be deduped"
    );
}

#[test]
fn test_kernel_export_into_library_search() {
    use crate::library::MathverseLibrary;
    use crate::search::{DomainQuery, MathverseSearch};
    use crate::trust::policy::TrustPolicy;

    let mut builder = KernelShardBuilder::new();
    builder
        .add_declaration(&make_prop_theorem("nn_verify.C001"), &["gamma-crown"])
        .unwrap();
    builder
        .add_declaration(&make_prop_theorem("PureMath.addComm"), &[])
        .unwrap();

    let bytes = builder.write_to_bytes().unwrap();
    let reader = ShardReader::from_bytes(&bytes).unwrap();

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&reader).unwrap();

    // Name lookup.
    assert!(lib.lookup_name("nn_verify.C001").is_some());
    assert!(lib.lookup_name("PureMath.addComm").is_some());

    // Domain search for NN verification.
    let nn_results = lib
        .search_domain(
            ContentDomain::NnVerification,
            &DomainQuery::NNArchitecture("C001".to_string()),
        )
        .unwrap();
    assert_eq!(nn_results.len(), 1);
    assert_eq!(
        nn_results[0].header.source_system,
        SourceSystem::CleanNative as u8
    );
}

/// Regression: universe-level parameter names must round-trip as a *contiguous*
/// run in the string table even when an earlier declaration already interned
/// some of those names. The shard format stores level params as a
/// `(start, count)` window and the reader reads `count` consecutive slots, so
/// routing the names through the deduplicating `add_string` (rather than
/// `add_string_block`) returned earlier, non-adjacent indices — the window then
/// read the WRONG names and reconstruction dropped a universe parameter, which
/// the checked `add_inductive` replay later rejected as "Undefined universe
/// level parameter 'v'". Because the string table's contents depend on env
/// iteration order, the corruption was intermittent (a shard either got lucky
/// with contiguous names or did not).
#[test]
fn test_kernel_export_level_params_contiguous_after_dedup() {
    use crate::shard_reconstruct::reconstruct_level_params;

    let mut builder = KernelShardBuilder::new();

    // Decl A pre-seeds the string table with the param names "u" and "v".
    let decl_a = Declaration::Theorem {
        name: Name::from_string("Test.declA"),
        level_params: vec![Name::from_string("u"), Name::from_string("v")],
        type_: Expr::sort(Level::zero()),
        value: Expr::sort(Level::zero()),
    };
    // Decl B reuses "u" (already interned by A) and introduces a fresh "w".
    // Under per-name dedup, "u" resolves to its earlier index and "w" lands far
    // away, so the (start, count) window for B reads ["u", "v"] — NOT ["u", "w"].
    let decl_b = Declaration::Theorem {
        name: Name::from_string("Test.declB"),
        level_params: vec![Name::from_string("u"), Name::from_string("w")],
        type_: Expr::sort(Level::zero()),
        value: Expr::sort(Level::zero()),
    };

    builder.add_declaration(&decl_a, &[]).unwrap();
    builder.add_declaration(&decl_b, &[]).unwrap();

    let bytes = builder.write_to_bytes().unwrap();
    let reader = ShardReader::from_bytes(&bytes).unwrap();

    let (_, hdr_b) = reader
        .lookup_name("Test.declB")
        .expect("declB should be findable");
    let params_b = reconstruct_level_params(
        &reader.strings,
        hdr_b.level_params_start,
        hdr_b.level_params_count,
    )
    .expect("reconstruct declB level params");
    assert_eq!(
        params_b,
        vec![Name::from_string("u"), Name::from_string("w")],
        "level params must round-trip as a contiguous run even when 'u' was pre-interned by declA"
    );

    // declA's params must still reconstruct correctly too.
    let (_, hdr_a) = reader
        .lookup_name("Test.declA")
        .expect("declA should be findable");
    let params_a = reconstruct_level_params(
        &reader.strings,
        hdr_a.level_params_start,
        hdr_a.level_params_count,
    )
    .expect("reconstruct declA level params");
    assert_eq!(
        params_a,
        vec![Name::from_string("u"), Name::from_string("v")]
    );
}
