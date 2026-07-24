// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Non-trivial end-to-end pipeline tests exercising real type-checking:
//! - Universe-polymorphic constants with level_params
//! - DeclKind coverage for all 8 variants
//!
//! Dependency-ordering and level-list tests live in
//! `tests_e2e_nontrivial_levels`.

use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_kernel::{Declaration, Environment, Name};

use crate::shard::{ShardReader, ShardWriter};
use crate::shard_reconstruct::{reconstruct_from_shard_with_level_lists, reconstruct_level_params};
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};
use crate::verify::incremental::verify_shard_incremental;

/// Helper: build an axiom header with standard metadata and given decl_kind/level_params.
fn make_axiom_header(
    name_idx: u32,
    type_idx: u32,
    decl_kind: DeclKind,
    level_params_start: u32,
    level_params_count: u16,
) -> MathverseConstantHeader {
    MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: decl_kind as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start,
        level_params_count,
        _pad2: [0u8; 26],
    }
}

/// Helper: write shard bytes from a ShardWriter.
fn write_shard(writer: &ShardWriter) -> (Vec<u8>, ShardReader) {
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();
    (buf, reader)
}

// ---------------------------------------------------------------------------
// Test 1: Universe-polymorphic constant (single param)
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_universe_polymorphic_constant() {
    let mut writer = ShardWriter::new();
    let name_id = writer.add_string("Poly.Id");
    let uparam_u = writer.add_string("u");

    let _l_zero = writer.add_level(FlatLevel::zero());
    let l_param_u = writer.add_level(FlatLevel::param(uparam_u));
    let l_succ_u = writer.add_level(FlatLevel::succ(l_param_u));
    let _sort_type_u = writer.add_expr(FlatExpr::sort(l_succ_u));
    let sort_u = writer.add_expr(FlatExpr::sort(l_param_u));
    let pi_type = writer.add_expr(FlatExpr::pi(0, sort_u, sort_u));

    writer.add_constant(make_axiom_header(
        name_id,
        pi_type,
        DeclKind::Axiom,
        uparam_u,
        1,
    ));
    let (_buf, reader) = write_shard(&writer);

    // Verify header stores level_params
    let hdr = &reader.constants[0];
    assert_eq!(hdr.level_params_count, 1, "should store 1 universe param");
    assert!(hdr.has_level_params(), "has_level_params() should be true");

    // Reconstruct level params
    let level_params = reconstruct_level_params(
        &reader.strings,
        hdr.level_params_start,
        hdr.level_params_count,
    )
    .unwrap();
    assert_eq!(level_params.len(), 1);
    assert_eq!(level_params[0].to_string(), "u");

    // Reconstruct type and verify it's a Pi
    let type_expr = reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        hdr.type_idx,
    )
    .unwrap();
    assert!(type_expr.is_pi(), "reconstructed type should be Pi");

    // Kernel accepts with real level_params
    let mut env = Environment::new();
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("Poly.Id"),
        level_params,
        type_: type_expr,
    });
    assert!(result.is_ok(), "kernel should accept: {:?}", result.err());
}

// ---------------------------------------------------------------------------
// Test 1b: Multiple universe params (u, v) with max level
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_multi_universe_params() {
    let mut writer = ShardWriter::new();
    let name_multi = writer.add_string("Poly.Multi");
    let uparam_u = writer.add_string("u");
    let uparam_v = writer.add_string("v");

    let _l_zero = writer.add_level(FlatLevel::zero());
    let l_param_u = writer.add_level(FlatLevel::param(uparam_u));
    let l_param_v = writer.add_level(FlatLevel::param(uparam_v));
    let l_max_uv = writer.add_level(FlatLevel::max(l_param_u, l_param_v));
    let sort_max_uv = writer.add_expr(FlatExpr::sort(l_max_uv));

    // "u" and "v" are consecutive in string table from uparam_u
    writer.add_constant(make_axiom_header(
        name_multi,
        sort_max_uv,
        DeclKind::Axiom,
        uparam_u,
        2,
    ));
    let (_buf, reader) = write_shard(&writer);

    let hdr = &reader.constants[0];
    assert_eq!(hdr.level_params_count, 2);

    let level_params = reconstruct_level_params(
        &reader.strings,
        hdr.level_params_start,
        hdr.level_params_count,
    )
    .unwrap();
    assert_eq!(level_params.len(), 2);
    assert_eq!(level_params[0].to_string(), "u");
    assert_eq!(level_params[1].to_string(), "v");

    let type_expr = reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        hdr.type_idx,
    )
    .unwrap();

    let mut env = Environment::new();
    let result = env.add_decl(Declaration::Axiom {
        name: Name::from_string("Poly.Multi"),
        level_params,
        type_: type_expr,
    });
    assert!(
        result.is_ok(),
        "kernel should accept multi-param: {:?}",
        result.err()
    );
}

// ---------------------------------------------------------------------------
// Test 2: DeclKind coverage — all 8 variants round-trip + is_inductive_family
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_decl_kind_coverage() {
    let all_kinds: [(DeclKind, &str, bool); 8] = [
        (DeclKind::Theorem, "DK.Theorem", false),
        (DeclKind::Definition, "DK.Definition", false),
        (DeclKind::Axiom, "DK.Axiom", false),
        (DeclKind::Opaque, "DK.Opaque", false),
        (DeclKind::Inductive, "DK.Inductive", true),
        (DeclKind::Constructor, "DK.Constructor", true),
        (DeclKind::Recursor, "DK.Recursor", true),
        (DeclKind::Quot, "DK.Quot", false),
    ];

    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    for (kind, name, _) in &all_kinds {
        let name_idx = writer.add_string(name);
        writer.add_constant(make_axiom_header(name_idx, sort_prop, *kind, 0, 0));
    }

    let (_buf, reader) = write_shard(&writer);
    assert_eq!(reader.constants.len(), 8);

    for (i, (expected_kind, name, expected_inductive)) in all_kinds.iter().enumerate() {
        let hdr = &reader.constants[i];
        let decoded = DeclKind::try_from(hdr.decl_kind).unwrap();
        assert_eq!(decoded, *expected_kind, "DeclKind mismatch for {name}");
        assert_eq!(
            hdr.is_inductive_family(),
            *expected_inductive,
            "is_inductive_family() wrong for {name}"
        );
    }

    let report = verify_shard_incremental(&reader);
    // All 8 constants are NO_VALUE. None is a genuine proof-check:
    //   - DK.Axiom and DK.Quot register as well-formed axioms  -> AxiomAccepted
    //   - DK.Theorem / DK.Definition / DK.Opaque have no value  -> AxiomFallback
    //   - DK.Inductive / DK.Constructor are unreplayable inductive skeletons
    //     that downgrade to kernel-checked STAND-IN axioms of their stated
    //     types (family_standins subset of axiom_fallback)
    //   - DK.Recursor is never stand-in eligible (an elimination principle is
    //     real logical strength) and fails closed                -> failed
    assert_eq!(
        report.kernel_verified, 0,
        "no value-bearing decls, so nothing is genuinely kernel-verified: {:?}",
        report.failures
    );
    assert_eq!(
        report.axiom_accepted, 2,
        "DK.Axiom + DK.Quot are accepted axioms: {:?}",
        report.failures
    );
    assert_eq!(
        report.axiom_fallback, 5,
        "DK.Theorem + DK.Definition + DK.Opaque fall back to axioms and \
         DK.Inductive + DK.Constructor to family stand-ins: {:?}",
        report.failures
    );
    assert_eq!(report.family_standins.len(), 2);
    assert_eq!(
        report.failed, 1,
        "the recursor skeleton fails closed: {:?}",
        report.failures
    );
}
