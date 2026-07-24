// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Environment-based `.olean` to `.mathverse` importer.

use super::*;

use clean_kernel::env::Environment;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{ConstantInfo, ConstantKind, Reducibility};

use crate::shard::ShardWriter;
use crate::types::{AxiomProfile, ImportConfidence, SourceSystem, NO_VALUE};

/// Create a minimal environment with the given constants.
fn mock_env(constants: Vec<ConstantInfo>) -> Environment {
    let mut env = Environment::default();
    env.extend_constants_unchecked(constants.into_iter());
    env
}

/// Create a constant with a simple Prop type and optional value.
fn simple_constant(name: &str, kind: ConstantKind, has_value: bool) -> ConstantInfo {
    let type_ = Expr::sort(Level::Zero);
    let value = if has_value {
        Some(Expr::sort(Level::Zero))
    } else {
        None
    };
    ConstantInfo::new_with_reducibility(
        Name::from_string(name),
        Vec::new(),
        type_,
        value,
        Reducibility::Regular(0),
        kind,
    )
}

#[test]
fn test_import_empty_environment() {
    let env = Environment::default();
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig::default();
    let (stats, records) = import_environment(&env, &mut writer, &config).unwrap();
    assert_eq!(stats.total, 0);
    assert_eq!(stats.imported(), 0);
    assert!(records.is_empty());
}

#[test]
fn test_import_single_theorem() {
    let ci = simple_constant("Nat.add_comm", ConstantKind::Theorem, true);
    let env = mock_env(vec![ci]);
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig::default();
    let (stats, records) = import_environment(&env, &mut writer, &config).unwrap();

    assert_eq!(stats.total, 1);
    assert_eq!(stats.kernel_verified, 1);
    assert_eq!(stats.axiomatized, 0);
    assert_eq!(stats.skipped, 0);
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].original_name, "Nat.add_comm");
}

#[test]
fn test_import_axiom_gets_axiomatized_profile() {
    let ci = simple_constant("Classical.choice", ConstantKind::Axiom, false);
    let env = mock_env(vec![ci]);
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig::default();
    let (stats, _records) = import_environment(&env, &mut writer, &config).unwrap();

    assert_eq!(stats.total, 1);
    assert_eq!(stats.axiomatized, 1);
    assert_eq!(stats.axiom_dependent, 1);
    assert_eq!(stats.trust_gated, 1);
}

#[test]
fn test_import_mixed_constants() {
    let constants = vec![
        simple_constant("Nat.add", ConstantKind::Definition, true),
        simple_constant("Nat.add_comm", ConstantKind::Theorem, true),
        simple_constant("Classical.choice", ConstantKind::Axiom, false),
        simple_constant("propext", ConstantKind::Axiom, false),
        simple_constant("SomeOpaque", ConstantKind::Opaque, false),
    ];
    let env = mock_env(constants);
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig::default();
    let (stats, _records) = import_environment(&env, &mut writer, &config).unwrap();

    assert_eq!(stats.total, 5);
    assert_eq!(stats.kernel_verified, 2); // Nat.add + Nat.add_comm
    assert_eq!(stats.axiomatized, 3); // Classical.choice + propext + SomeOpaque
    assert_eq!(stats.skipped, 0);
}

#[test]
fn test_axiom_profile_classical_choice() {
    let ci = simple_constant("Classical.choice", ConstantKind::Axiom, false);
    let profile = compute_env_axiom_profile(&ci);
    assert!(profile.has(AxiomProfile::CHOICE));
    assert!(profile.has(AxiomProfile::CLASSICAL));
    assert!(profile.has(AxiomProfile::AXIOMATIZED));
    assert!(profile.is_trust_gated());
}

#[test]
fn test_axiom_profile_propext() {
    let ci = simple_constant("propext", ConstantKind::Axiom, false);
    let profile = compute_env_axiom_profile(&ci);
    assert!(profile.has(AxiomProfile::PROP_EXT));
    assert!(profile.has(AxiomProfile::AXIOMATIZED));
    assert!(!profile.has(AxiomProfile::CHOICE));
}

#[test]
fn test_axiom_profile_quot() {
    for name in &["Quot", "Quot.mk", "Quot.ind", "Quot.lift"] {
        let ci = simple_constant(name, ConstantKind::Definition, true);
        let profile = compute_env_axiom_profile(&ci);
        assert!(
            profile.has(AxiomProfile::QUOT),
            "{name} should have QUOT bit"
        );
    }
}

#[test]
fn test_axiom_profile_theorem_pure() {
    let ci = simple_constant("Nat.add_comm", ConstantKind::Theorem, true);
    let profile = compute_env_axiom_profile(&ci);
    assert!(profile.is_pure());
    assert!(!profile.is_trust_gated());
}

#[test]
fn test_import_filters_private_constants() {
    let constants = vec![
        simple_constant("Foo._private.bar", ConstantKind::Definition, true),
        simple_constant("Foo.pub_fn", ConstantKind::Definition, true),
    ];
    let env = mock_env(constants);
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig::default(); // include_private = false
    let (stats, records) = import_environment(&env, &mut writer, &config).unwrap();

    assert_eq!(stats.total, 2);
    assert_eq!(stats.skipped, 1);
    assert_eq!(stats.kernel_verified, 1);
    assert!(records
        .iter()
        .any(|r| r.notes.iter().any(|n| n.contains("private"))));
}

#[test]
fn test_import_includes_private_when_configured() {
    let constants = vec![simple_constant(
        "Foo._private.bar",
        ConstantKind::Definition,
        true,
    )];
    let env = mock_env(constants);
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig {
        include_private: true,
        ..Default::default()
    };
    let (stats, _records) = import_environment(&env, &mut writer, &config).unwrap();

    assert_eq!(stats.total, 1);
    assert_eq!(stats.skipped, 0);
    assert_eq!(stats.kernel_verified, 1);
}

#[test]
fn test_import_writes_shard() {
    let constants = vec![
        simple_constant("Nat.add", ConstantKind::Definition, true),
        simple_constant("propext", ConstantKind::Axiom, false),
    ];
    let env = mock_env(constants);
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig::default();
    import_environment(&env, &mut writer, &config).unwrap();

    // Write to buffer and read back.
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

    assert_eq!(reader.header.constant_count, 2);

    // Check that constant names are correct (sorted order).
    let names: Vec<&str> = reader
        .constants
        .iter()
        .map(|c| reader.strings[c.name_idx as usize].as_str())
        .collect();
    assert!(names.contains(&"Nat.add"));
    assert!(names.contains(&"propext"));

    // Check source system.
    for c in &reader.constants {
        assert_eq!(c.source_system, SourceSystem::Lean4 as u8);
    }
}

/// Regression: universe-polymorphic `Const` references must round-trip WITH
/// their level arguments through the shard's `level_lists` table.
///
/// A stale exporter discarded the lowered levels and wrote `u32::MAX` (no
/// levels) for every `Const(T, [u])`, collapsing it to `Const(T, [])`. On
/// reconstruction `T` was applied to zero level args, so every reference to a
/// universe-polymorphic constant failed with "Level count mismatch for T:
/// declared N level params, got 0" (observed: 15,204/15,603 real Init round-trip
/// failures). This test exports `D.{u} := C.{u}` and asserts the reconstructed
/// value keeps its one universe argument AND that `verify_shard_into_env`
/// accepts `D`.
#[test]
fn test_import_preserves_const_reference_level_lists() {
    let u = Name::from_string("u");
    // C.{u} : Sort u   (universe-polymorphic axiom)
    let c = ConstantInfo::new_with_reducibility(
        Name::from_string("C_poly"),
        vec![u.clone()],
        Expr::sort(Level::param(u.clone())),
        None,
        Reducibility::Regular(0),
        ConstantKind::Axiom,
    );
    // D.{u} : Sort u := C.{u}   (references C with an explicit level arg)
    let d = ConstantInfo::new_with_reducibility(
        Name::from_string("D_uses_c"),
        vec![u.clone()],
        Expr::sort(Level::param(u.clone())),
        Some(Expr::const_(
            Name::from_string("C_poly"),
            vec![Level::param(u.clone())],
        )),
        Reducibility::Regular(0),
        ConstantKind::Definition,
    );
    let env = mock_env(vec![c, d]);

    let mut writer = ShardWriter::new();
    let config = EnvImportConfig::default();
    import_environment(&env, &mut writer, &config).unwrap();
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

    // Reconstruct D's value: it must be `Const("C_poly", [u])` — one universe
    // argument, NOT the collapsed zero-level form.
    let d_header = reader
        .constants
        .iter()
        .find(|c| reader.strings.get(c.name_idx as usize).map(String::as_str) == Some("D_uses_c"))
        .expect("D_uses_c present in shard");
    let value = crate::shard_reconstruct::reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        d_header.value_idx,
    )
    .expect("reconstruct D value");
    match value.kind() {
        clean_kernel::expr::ExprKind::Const(name, levels) => {
            assert_eq!(name.to_string(), "C_poly");
            assert_eq!(
                levels.len(),
                1,
                "const reference must retain its single universe argument",
            );
        }
        other => panic!("expected Const(C_poly, [u]), got {other:?}"),
    }

    // End-to-end: the rebuilt env must accept D (its value `C.{u}` resolves
    // against C's one declared level param).
    let mut rebuilt = Environment::new();
    let result = crate::lean4::shard_verify::verify_shard_into_env(&reader, &mut rebuilt)
        .expect("verify_shard_into_env");
    assert!(
        !result.failures.iter().any(|(n, _)| n == "D_uses_c"),
        "D must not fail reconstruction; failures = {:?}",
        result.failures,
    );
}

/// Regression: env→shard export must tag inductive-family members with the
/// right `DeclKind` and stamp the inductive root's `num_params`, driven by the
/// kernel's `get_inductive`/`get_constructor`/`get_recursor` registries — NOT
/// by `ConstantKind` (which only knows Definition/Theorem/Opaque/Axiom, so a
/// value-less inductive would otherwise be mislabelled Axiom).
///
/// Without this, `verify_shard_incremental` cannot group or checked-replay a
/// family: it drops every family to an axiom fallback and withholds trust from
/// dependents. On the real Lean 4.30 Init env this stamp raised the incremental
/// KernelVerified count from 2,899 to 13,894 / 15,603 (axiom-fallbacks 5,692 ->
/// 559).
/// Regression: a Nat literal exceeding u64::MAX (e.g. `UInt64.size = 2^64`)
/// must round-trip through env→shard export as a `NAT_BIG` limb string, not be
/// dropped. The old code errored out on any nat > u64::MAX, so the constant was
/// skipped and every dependent (all of UInt64/USize arithmetic) failed with
/// "Unknown constant". Matches the canonical `clean_kernel::flat::convert` /
/// production `alpha.rs` encoding.
#[test]
fn test_import_preserves_big_nat_literal() {
    use clean_kernel::expr::{ExprKind, Literal};

    // value = 2^64 = u64::MAX + 1 — does not fit FlatExpr's inline u64.
    let big_value = Expr::nat_lit_u128(1u128 << 64);
    let ci = ConstantInfo::new_with_reducibility(
        Name::from_string("BigConst"),
        Vec::new(),
        Expr::const_(Name::from_string("Nat"), Vec::<Level>::new()),
        Some(big_value),
        Reducibility::Regular(0),
        ConstantKind::Definition,
    );
    let env = mock_env(vec![ci]);

    let mut writer = ShardWriter::new();
    import_environment(&env, &mut writer, &EnvImportConfig::default()).unwrap();
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

    let header = reader
        .constants
        .iter()
        .find(|c| reader.strings.get(c.name_idx as usize).map(String::as_str) == Some("BigConst"))
        .expect("BigConst must be exported, not dropped");
    let value = crate::shard_reconstruct::reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        header.value_idx,
    )
    .expect("reconstruct BigConst value");
    match value.kind() {
        ExprKind::Lit(Literal::Nat(n)) => {
            assert_eq!(
                n.to_u64(),
                None,
                "2^64 must stay a big nat, not truncate to u64"
            );
            assert_eq!(
                n.limbs(),
                &[0u64, 1u64][..],
                "2^64 = limbs [0, 1] little-endian"
            );
        }
        other => panic!("expected a big Nat literal, got {other:?}"),
    }
}

#[test]
fn test_import_stamps_inductive_family_metadata() {
    use clean_kernel::{Constructor, InductiveDecl, InductiveType};

    // `Flag : Type` with two nullary constructors.
    let flag = Name::from_string("Flag");
    let ctor = |n: &str| Constructor {
        name: Name::from_string(n),
        type_: Expr::const_(flag.clone(), Vec::<Level>::new()),
    };
    let decl = InductiveDecl {
        level_params: Vec::new(),
        num_params: 0,
        types: vec![InductiveType {
            name: flag.clone(),
            type_: Expr::sort(Level::succ(Level::zero())), // Type = Sort 1
            constructors: vec![ctor("Flag.a"), ctor("Flag.b")],
        }],
    };
    let mut env = Environment::default();
    env.add_inductive(decl).expect("Flag family adds");

    let mut writer = ShardWriter::new();
    import_environment(&env, &mut writer, &EnvImportConfig::default()).unwrap();
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

    let header = |name: &str| {
        reader
            .constants
            .iter()
            .find(|c| reader.strings.get(c.name_idx as usize).map(String::as_str) == Some(name))
            .unwrap_or_else(|| panic!("{name} present in shard"))
    };

    let flag_h = header("Flag");
    assert_eq!(
        flag_h.decl_kind,
        crate::types::DeclKind::Inductive as u8,
        "inductive type must carry DeclKind::Inductive (registry-driven), not Axiom",
    );
    assert_eq!(
        flag_h.inductive_decl_num_params(),
        Some(0),
        "inductive root must carry the typed num_params stamp",
    );
    assert_eq!(
        header("Flag.a").decl_kind,
        crate::types::DeclKind::Constructor as u8,
    );
    assert_eq!(
        header("Flag.b").decl_kind,
        crate::types::DeclKind::Constructor as u8,
    );
    assert_eq!(
        header("Flag.rec").decl_kind,
        crate::types::DeclKind::Recursor as u8,
    );
}

#[test]
fn test_export_to_file() {
    let ci = simple_constant("test.thm", ConstantKind::Theorem, true);
    let env = mock_env(vec![ci]);
    let config = EnvImportConfig {
        source_file: Some("test.olean".to_string()),
        source_version: Some("Lean 4.3.0".to_string()),
        ..Default::default()
    };

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("lean4.mathverse");
    let stats = export_environment_to_file(&env, &path, &config).unwrap();

    assert_eq!(stats.total, 1);
    assert_eq!(stats.kernel_verified, 1);

    // Verify the file is readable.
    let reader = crate::shard::ShardReader::from_file(&path).unwrap();
    assert_eq!(reader.header.constant_count, 1);
}

// REGRESSION (#6 proof-value elision vs provenance sidecar): an environment
// whose Theorem/Opaque proof VALUES were dropped by `elide_proof_values`
// (the post-hoc null that conversion-time elision feeds into) must still export
// a `.mathverse` shard whose provenance sidecar ROUND-TRIPS. Each constant —
// value-bearing or value-elided — contributes exactly one provenance record and
// one header, so `validate_provenance_headers` (invoked inside
// `ShardReader::from_bytes`) must decode the sidecar cleanly under every elision
// policy. A desync would surface as a bincode `UnexpectedEnd` decode error.
#[test]
fn test_elided_env_shard_provenance_round_trips_all_policies() {
    use clean_kernel::env::ProofValueElision;

    let make_env = || {
        mock_env(vec![
            simple_constant("Nat.add", ConstantKind::Definition, true),
            simple_constant("thm_a", ConstantKind::Theorem, true),
            simple_constant("thm_b", ConstantKind::Theorem, true),
            simple_constant("op_a", ConstantKind::Opaque, true),
            simple_constant("Classical.choice", ConstantKind::Axiom, false),
        ])
    };

    for policy in [
        ProofValueElision::None,
        ProofValueElision::OpaqueOnly,
        ProofValueElision::OpaqueAndTheorem,
    ] {
        let mut env = make_env();
        env.elide_proof_values(policy);

        let mut writer = ShardWriter::new();
        let config = EnvImportConfig::default();
        let (stats, records) = import_environment(&env, &mut writer, &config)
            .unwrap_or_else(|e| panic!("export under {policy:?} failed: {e}"));
        assert_eq!(
            stats.total, 5,
            "all constants accounted for under {policy:?}"
        );
        assert_eq!(records.len(), 5, "one record per constant under {policy:?}");

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();

        // The load path decodes + validates the provenance sidecar; a desync
        // between elided and non-elided constants would fail here.
        let reader = crate::shard::ShardReader::from_bytes(&buf)
            .unwrap_or_else(|e| panic!("shard round-trip under {policy:?} failed: {e}"));
        assert_eq!(reader.header.constant_count, 5);

        // The provenance sidecar must decode and carry one record per constant.
        let sidecar = crate::provenance::ProvenanceSidecar::from_bytes(&reader.provenance)
            .unwrap_or_else(|e| panic!("provenance decode under {policy:?} failed: {e}"));
        assert_eq!(
            sidecar.len(),
            reader.header.constant_count as usize,
            "sidecar record count must equal constant count under {policy:?}"
        );

        // Every header's provenance link must resolve and its digest must match.
        for (i, c) in reader.constants.iter().enumerate() {
            assert!(
                sidecar.get(c.provenance_idx).is_some(),
                "constant {i} provenance_idx out of bounds under {policy:?}"
            );
            assert!(
                sidecar.verify_digest(c),
                "constant {i} sidecar digest mismatch under {policy:?}"
            );
        }
    }
}

#[test]
fn test_confidence_theorem_with_proof() {
    let ci = simple_constant("thm", ConstantKind::Theorem, true);
    assert_eq!(confidence_for(&ci), ImportConfidence::KernelVerified);
}

#[test]
fn test_confidence_theorem_without_proof() {
    let ci = simple_constant("thm", ConstantKind::Theorem, false);
    assert_eq!(confidence_for(&ci), ImportConfidence::Axiomatized);
}

#[test]
fn test_confidence_axiom() {
    let ci = simple_constant("ax", ConstantKind::Axiom, false);
    assert_eq!(confidence_for(&ci), ImportConfidence::Axiomatized);
}

#[test]
fn test_confidence_opaque() {
    let ci = simple_constant("op", ConstantKind::Opaque, false);
    assert_eq!(confidence_for(&ci), ImportConfidence::Axiomatized);
}

#[test]
fn test_confidence_definition_with_value() {
    let ci = simple_constant("def", ConstantKind::Definition, true);
    assert_eq!(confidence_for(&ci), ImportConfidence::KernelVerified);
}

#[test]
fn test_stats_imported() {
    let stats = EnvImportStats {
        total: 10,
        kernel_verified: 7,
        axiomatized: 2,
        skipped: 1,
        axiom_dependent: 3,
        trust_gated: 2,
    };
    assert_eq!(stats.imported(), 9);
}

#[test]
fn test_import_with_complex_types() {
    // Create a constant with Pi type: (x : Prop) -> Prop
    let prop = Expr::sort(Level::Zero);
    let pi_type = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());
    let ci = ConstantInfo::new_with_reducibility(
        Name::from_string("id_prop"),
        Vec::new(),
        pi_type,
        Some(Expr::lam(BinderInfo::Default, prop.clone(), Expr::bvar(0))),
        Reducibility::Reducible,
        ConstantKind::Definition,
    );

    let env = mock_env(vec![ci]);
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig::default();
    let (stats, _records) = import_environment(&env, &mut writer, &config).unwrap();

    assert_eq!(stats.total, 1);
    assert_eq!(stats.kernel_verified, 1);

    // Verify the expressions survived lowering.
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(reader.header.constant_count, 1);
    assert!(reader.header.expr_count > 0);
    assert!(reader.header.level_count > 0);
}

#[test]
fn test_provenance_records_populated() {
    let constants = vec![
        simple_constant("thm1", ConstantKind::Theorem, true),
        simple_constant("thm2", ConstantKind::Theorem, true),
    ];
    let env = mock_env(constants);
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig {
        source_file: Some("Init.olean".to_string()),
        source_version: Some("Lean 4.3.0".to_string()),
        ..Default::default()
    };
    let (_stats, records) = import_environment(&env, &mut writer, &config).unwrap();

    assert_eq!(records.len(), 2);
    for record in &records {
        assert_eq!(record.source_file.as_deref(), Some("Init.olean"));
        assert_eq!(record.source_version.as_deref(), Some("Lean 4.3.0"));
        assert_eq!(record.pipeline_version, 1);
        assert!(!record.notes.is_empty());
    }
}

#[test]
fn test_round_trip_type_indices_valid() {
    // Verify that type_idx/value_idx in headers reference valid
    // expressions in the shard reader's arena.
    let constants = vec![
        simple_constant("foo", ConstantKind::Definition, true),
        simple_constant("bar", ConstantKind::Theorem, true),
    ];
    let env = mock_env(constants);
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig::default();
    import_environment(&env, &mut writer, &config).unwrap();

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

    for c in &reader.constants {
        // type_idx must be within the expression count.
        assert!(
            (c.type_idx as usize) < reader.header.expr_count as usize,
            "type_idx {} out of range (expr_count={})",
            c.type_idx,
            reader.header.expr_count
        );
        // value_idx must be within range or NO_VALUE.
        if c.value_idx != NO_VALUE {
            assert!(
                (c.value_idx as usize) < reader.header.expr_count as usize,
                "value_idx {} out of range (expr_count={})",
                c.value_idx,
                reader.header.expr_count
            );
        }
    }
}

#[test]
fn test_lowering_level_zero() {
    let mut writer = ShardWriter::new();
    let mut ctx = KernelLoweringCtx::new(&mut writer);
    let idx = ctx.lower_level(&Level::Zero);
    assert_eq!(idx, 0);
}

#[test]
fn test_lowering_level_succ() {
    let mut writer = ShardWriter::new();
    let mut ctx = KernelLoweringCtx::new(&mut writer);
    let idx = ctx.lower_level(&Level::Succ(std::sync::Arc::new(Level::Zero)));
    assert!(idx > 0);
}

#[test]
fn test_lowering_expr_bvar() {
    let mut writer = ShardWriter::new();
    let mut ctx = KernelLoweringCtx::new(&mut writer);
    let expr = Expr::bvar(42);
    let idx = ctx.lower_expr(&expr).unwrap();
    assert_eq!(idx, 0); // First expr added.
}

#[test]
fn test_lowering_expr_sort() {
    let mut writer = ShardWriter::new();
    let mut ctx = KernelLoweringCtx::new(&mut writer);
    let expr = Expr::sort(Level::Zero);
    let idx = ctx.lower_expr(&expr).unwrap();
    assert_eq!(idx, 0); // First expr.
}

#[test]
fn test_lowering_context_intern_dedup() {
    let mut writer = ShardWriter::new();
    let mut ctx = KernelLoweringCtx::new(&mut writer);
    let idx1 = ctx.intern_string("hello");
    let idx2 = ctx.intern_string("hello");
    let idx3 = ctx.intern_string("world");
    assert_eq!(idx1, idx2, "same string should return same index");
    assert_ne!(
        idx1, idx3,
        "different strings should return different indices"
    );
}

// ---------------------------------------------------------------------------
// Level params preservation tests (#3413)
// ---------------------------------------------------------------------------

/// Create a constant with specific level_params (universe variables).
fn constant_with_levels(
    name: &str,
    kind: ConstantKind,
    has_value: bool,
    level_params: Vec<&str>,
) -> ConstantInfo {
    let type_ = Expr::sort(Level::Zero);
    let value = if has_value {
        Some(Expr::sort(Level::Zero))
    } else {
        None
    };
    ConstantInfo::new_with_reducibility(
        Name::from_string(name),
        level_params.into_iter().map(Name::from_string).collect(),
        type_,
        value,
        Reducibility::Regular(0),
        kind,
    )
}

#[test]
fn test_env_import_preserves_single_level_param() {
    let ci = constant_with_levels("List.length", ConstantKind::Definition, true, vec!["u"]);
    let env = mock_env(vec![ci]);
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig::default();
    import_environment(&env, &mut writer, &config).unwrap();

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

    assert_eq!(reader.constants.len(), 1);
    let c = &reader.constants[0];
    assert_eq!(c.level_params_count, 1);
    assert!(c.has_level_params());
    assert_eq!(&reader.strings[c.level_params_start as usize], "u");
}

#[test]
fn test_env_import_preserves_multiple_level_params() {
    let ci = constant_with_levels("List.map", ConstantKind::Definition, true, vec!["u", "v"]);
    let env = mock_env(vec![ci]);
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig::default();
    import_environment(&env, &mut writer, &config).unwrap();

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

    let c = &reader.constants[0];
    assert_eq!(c.level_params_count, 2);
    let start = c.level_params_start as usize;
    assert_eq!(&reader.strings[start], "u");
    assert_eq!(&reader.strings[start + 1], "v");
}

#[test]
fn test_env_import_zero_level_params_when_empty() {
    let ci = simple_constant("Nat.add", ConstantKind::Definition, true);
    let env = mock_env(vec![ci]);
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig::default();
    import_environment(&env, &mut writer, &config).unwrap();

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

    let c = &reader.constants[0];
    assert_eq!(c.level_params_count, 0);
    assert!(!c.has_level_params());
}

#[test]
fn test_env_import_level_params_mixed_constants() {
    let constants = vec![
        constant_with_levels("List.map", ConstantKind::Definition, true, vec!["u", "v"]),
        simple_constant("Nat.add", ConstantKind::Definition, true),
        constant_with_levels("Option.map", ConstantKind::Definition, true, vec!["w"]),
    ];
    let env = mock_env(constants);
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig::default();
    import_environment(&env, &mut writer, &config).unwrap();

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

    // Constants are sorted by name, so: List.map, Nat.add, Option.map
    let names: Vec<&str> = reader
        .constants
        .iter()
        .map(|c| reader.strings[c.name_idx as usize].as_str())
        .collect();

    let list_map_idx = names
        .iter()
        .position(|n| *n == "List.map")
        .expect("List.map");
    let nat_add_idx = names.iter().position(|n| *n == "Nat.add").expect("Nat.add");
    let option_map_idx = names
        .iter()
        .position(|n| *n == "Option.map")
        .expect("Option.map");

    // List.map: [u, v]
    let c_lm = &reader.constants[list_map_idx];
    assert_eq!(c_lm.level_params_count, 2);
    assert_eq!(&reader.strings[c_lm.level_params_start as usize], "u");
    assert_eq!(&reader.strings[c_lm.level_params_start as usize + 1], "v");

    // Nat.add: no level params
    let c_na = &reader.constants[nat_add_idx];
    assert_eq!(c_na.level_params_count, 0);

    // Option.map: [w]
    let c_om = &reader.constants[option_map_idx];
    assert_eq!(c_om.level_params_count, 1);
    assert_eq!(&reader.strings[c_om.level_params_start as usize], "w");
}
