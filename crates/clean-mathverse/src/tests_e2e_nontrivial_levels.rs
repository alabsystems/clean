// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Non-trivial end-to-end pipeline tests (part 2):
//! - Dependency-ordered verification with real type references
//! - Level lists on Const expressions round-tripping through shard

use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_kernel::{Declaration, Environment, Name};

use crate::shard::{ShardReader, ShardWriter};
use crate::shard_reconstruct::{reconstruct_from_shard, reconstruct_from_shard_with_level_lists};
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
// Test 3: Non-trivial dependency — B's type references A as a Const node
// ---------------------------------------------------------------------------

/// Build shard with A : Type 0, B : (A -> Prop). Returns (bytes, reader).
fn build_dependency_shard() -> (Vec<u8>, ShardReader) {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let l1 = writer.add_level(FlatLevel::succ(l0));
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));
    let sort_type = writer.add_expr(FlatExpr::sort(l1));

    let name_a = writer.add_string("Dep.A");
    writer.add_constant(make_axiom_header(name_a, sort_type, DeclKind::Axiom, 0, 0));

    let name_b = writer.add_string("Dep.B");
    let const_a = writer.add_expr(FlatExpr::const_ref(name_a, u32::MAX));
    let pi_a_prop = writer.add_expr(FlatExpr::pi(0, const_a, sort_prop));
    writer.add_constant(make_axiom_header(name_b, pi_a_prop, DeclKind::Axiom, 0, 0));

    write_shard(&writer)
}

#[test]
fn test_e2e_nontrivial_type_dependency_incremental() {
    let (_buf, reader) = build_dependency_shard();
    let report = verify_shard_incremental(&reader);
    // Dep.A and Dep.B are both NO_VALUE axioms: the kernel accepts their types
    // (Dep.B's type references Dep.A, which resolves in incremental order) but
    // there is no proof term, so they are AxiomAccepted, not KernelVerified.
    assert_eq!(
        report.axiom_accepted, 2,
        "both axioms should be accepted (dependency resolves): {:?}",
        report.failures
    );
    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.failed, 0);
}

#[test]
fn test_e2e_nontrivial_type_dependency_order_matters() {
    let (_buf, reader) = build_dependency_shard();

    // B succeeds after A is in environment
    let mut env = Environment::new();
    let type_a = reconstruct_from_shard(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        reader.constants[0].type_idx,
    )
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Dep.A"),
        level_params: vec![],
        type_: type_a,
    })
    .expect("A should be accepted");

    let type_b = reconstruct_from_shard(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        reader.constants[1].type_idx,
    )
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Dep.B"),
        level_params: vec![],
        type_: type_b.clone(),
    })
    .expect("B should be accepted after A");

    // B fails WITHOUT A
    let mut env_empty = Environment::new();
    let result = env_empty.add_decl(Declaration::Axiom {
        name: Name::from_string("Dep.B"),
        level_params: vec![],
        type_: type_b,
    });
    assert!(
        result.is_err(),
        "B should FAIL without A (type references unknown const)"
    );
}

// ---------------------------------------------------------------------------
// Test 4: Level lists in expressions — Const nodes carry universe arguments
// ---------------------------------------------------------------------------

/// Build shard: MyType.{u} : Type u, User.{u} : MyType.{u} -> Prop
fn build_level_list_shard() -> (Vec<u8>, ShardReader, u32) {
    let mut writer = ShardWriter::new();
    let name_my_type = writer.add_string("LevelList.MyType");
    let name_user = writer.add_string("LevelList.User");
    let uparam_u = writer.add_string("u");

    let l_zero = writer.add_level(FlatLevel::zero());
    let l_param_u = writer.add_level(FlatLevel::param(uparam_u));
    let l_succ_u = writer.add_level(FlatLevel::succ(l_param_u));
    let ll_u = writer.add_level_list(&[l_param_u]);

    let sort_type_u = writer.add_expr(FlatExpr::sort(l_succ_u));
    let sort_prop = writer.add_expr(FlatExpr::sort(l_zero));

    writer.add_constant(make_axiom_header(
        name_my_type,
        sort_type_u,
        DeclKind::Axiom,
        uparam_u,
        1,
    ));

    let const_mytype_u = writer.add_expr(FlatExpr::const_ref(name_my_type, ll_u));
    let pi_mytype_prop = writer.add_expr(FlatExpr::pi(0, const_mytype_u, sort_prop));
    writer.add_constant(make_axiom_header(
        name_user,
        pi_mytype_prop,
        DeclKind::Axiom,
        uparam_u,
        1,
    ));

    let (buf, reader) = write_shard(&writer);
    (buf, reader, ll_u)
}

#[test]
fn test_e2e_level_lists_shard_structure() {
    let (_buf, reader, ll_u) = build_level_list_shard();

    assert!(
        !reader.level_lists.is_empty(),
        "level_lists should be non-empty"
    );
    assert!(
        reader.header.level_lists_count > 0,
        "header level_lists_count > 0"
    );

    // Level list at offset ll_u: [count=1, level_idx_for_param_u]
    let offset = ll_u as usize;
    assert_eq!(
        reader.level_lists[offset], 1,
        "level list count should be 1"
    );
}

#[test]
fn test_e2e_level_lists_reconstruct_and_kernel() {
    let (_buf, reader, _ll_u) = build_level_list_shard();

    // Reconstruct User's type — should contain Param level
    let user_hdr = &reader.constants[1];
    let user_type = reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        user_hdr.type_idx,
    )
    .unwrap();
    let dbg = format!("{user_type:?}");
    assert!(
        dbg.contains("MyType") && dbg.contains("Param"),
        "should have MyType+Param: {dbg}"
    );

    // Both constants accepted by kernel with level params
    let mut env = Environment::new();
    let u_name = Name::from_string("u");
    let mytype_type = reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        reader.constants[0].type_idx,
    )
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("LevelList.MyType"),
        level_params: vec![u_name.clone()],
        type_: mytype_type,
    })
    .expect("MyType should be accepted");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("LevelList.User"),
        level_params: vec![u_name],
        type_: user_type,
    })
    .expect("User should be accepted (references MyType.{u})");
}

// ---------------------------------------------------------------------------
// Test 4b: Empty level list sentinel + deduplication
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_empty_level_list_sentinel() {
    let mut writer = ShardWriter::new();
    let empty_ll = writer.add_level_list(&[]);
    assert_eq!(empty_ll, u32::MAX, "empty level list should be sentinel");

    let name_idx = writer.add_string("Empty.Const");
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));
    let const_empty = writer.add_expr(FlatExpr::const_ref(name_idx, u32::MAX));

    writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx: sort_prop,
        value_idx: const_empty,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Axiom as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    let (_buf, reader) = write_shard(&writer);
    let val = reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        reader.constants[0].value_idx,
    )
    .unwrap();
    let val_str = format!("{val:?}");
    assert!(
        val_str.contains("Const") && val_str.contains("Empty"),
        "got: {val_str}"
    );
}

#[test]
fn test_e2e_level_list_dedup() {
    let mut writer = ShardWriter::new();
    let uparam_u = writer.add_string("u");
    let l_param_u = writer.add_level(FlatLevel::param(uparam_u));

    let ll1 = writer.add_level_list(&[l_param_u]);
    let ll2 = writer.add_level_list(&[l_param_u]);
    assert_eq!(ll1, ll2, "identical lists should dedup");

    let l_zero = writer.add_level(FlatLevel::zero());
    let ll3 = writer.add_level_list(&[l_zero]);
    assert_ne!(ll1, ll3, "different lists should differ");

    let ll4 = writer.add_level_list(&[l_param_u, l_zero]);
    let ll5 = writer.add_level_list(&[l_param_u, l_zero]);
    assert_eq!(ll4, ll5, "multi-element dedup");
    assert_ne!(ll4, ll1, "different-length should differ");
}
