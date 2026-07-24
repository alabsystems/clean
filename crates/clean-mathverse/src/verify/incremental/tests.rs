// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::{HashMap, HashSet};

use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_kernel::{Declaration, Environment, Expr, Level, Name};

use crate::shard::{ShardReader, ShardWriter};
use crate::shard_reconstruct::reconstruct_from_shard_with_level_lists;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

use super::{
    build_dependency_graph, build_value_bearing_decl, bump_recursor_motive_levels,
    fix_recursor_level_counts, is_concrete_level_numeral, is_int63_primitive_stuck_rejection,
    is_stuck_native_primitive, is_universe_collapse_rejection, mentions_primitive_bearing_const,
    plan_incremental_recheck, retry_speculative_motive_universe, topological_sort,
    types_eq_modulo_universe, verify_shard_incremental, verify_shard_incremental_recheck,
    verify_shard_incremental_with_env, AddConstResult,
};

/// Helper: build a shard from (name, dependency_names) specs.
/// Types are Sort(0), values (when deps present) are Const-ref chains.
fn build_test_shard(specs: &[(&str, &[&str])]) -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let mut name_indices: Vec<u32> = Vec::new();
    for (name, _) in specs {
        name_indices.push(writer.add_string(name));
    }

    for (i, (_, deps)) in specs.iter().enumerate() {
        if deps.is_empty() {
            writer.add_constant(MathverseConstantHeader {
                name_idx: name_indices[i],
                type_idx: sort_prop,
                value_idx: NO_VALUE,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        } else {
            let dep_str_indices: Vec<u32> = deps.iter().map(|d| writer.add_string(d)).collect();
            let mut val = writer.add_expr(FlatExpr::const_ref(dep_str_indices[0], u32::MAX));
            for &dep_idx in &dep_str_indices[1..] {
                let next = writer.add_expr(FlatExpr::const_ref(dep_idx, u32::MAX));
                val = writer.add_expr(FlatExpr::app(val, next));
            }
            writer.add_constant(MathverseConstantHeader {
                name_idx: name_indices[i],
                type_idx: sort_prop,
                value_idx: val,
                source_system: SourceSystem::Lean4 as u8,
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }
    }

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

/// Build a small shard with kernel-valid definitions:
/// `P : Prop`, `idP : P -> P`, `applyId : P -> P`.
fn build_valid_definition_chain_shard() -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let p_name = writer.add_string("P");
    let id_name = writer.add_string("idP");
    let apply_name = writer.add_string("applyId");

    let p_const = writer.add_expr(FlatExpr::const_ref(p_name, u32::MAX));
    let p_to_p = writer.add_expr(FlatExpr::pi(0, p_const, p_const));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    let id_value = writer.add_expr(FlatExpr::lam(0, p_const, bvar0));
    let id_const = writer.add_expr(FlatExpr::const_ref(id_name, u32::MAX));
    let apply_body = writer.add_expr(FlatExpr::app(id_const, bvar0));
    let apply_value = writer.add_expr(FlatExpr::lam(0, p_const, apply_body));

    writer.add_constant(MathverseConstantHeader {
        name_idx: p_name,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
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

    writer.add_constant(MathverseConstantHeader {
        name_idx: id_name,
        type_idx: p_to_p,
        value_idx: id_value,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Definition as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    writer.add_constant(MathverseConstantHeader {
        name_idx: apply_name,
        type_idx: p_to_p,
        value_idx: apply_value,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Definition as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

/// Build a kernel-valid zero-parameter inductive family:
/// `ReplayNat : Type`, `ReplayNat.zero : ReplayNat`,
/// `ReplayNat.succ : ReplayNat -> ReplayNat`.
fn build_simple_inductive_replay_shard() -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let l1 = writer.add_level(FlatLevel::succ(l0));
    let sort_type = writer.add_expr(FlatExpr::sort(l1));

    let ind_name = writer.add_string("ReplayNat");
    let zero_name = writer.add_string("ReplayNat.zero");
    let succ_name = writer.add_string("ReplayNat.succ");

    let replay_nat = writer.add_expr(FlatExpr::const_ref(ind_name, u32::MAX));
    let succ_type = writer.add_expr(FlatExpr::pi(0, replay_nat, replay_nat));

    writer.add_constant(MathverseConstantHeader {
        name_idx: ind_name,
        type_idx: sort_type,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Inductive as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    writer.add_constant(MathverseConstantHeader {
        name_idx: zero_name,
        type_idx: replay_nat,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Constructor as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    writer.add_constant(MathverseConstantHeader {
        name_idx: succ_name,
        type_idx: succ_type,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Constructor as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

/// Build a kernel-valid parameterized single-type inductive family:
/// `ReplayList.{u} (alpha : Sort u) : Sort u`,
/// `ReplayList.nil : (alpha : Sort u) -> ReplayList alpha`, and
/// `ReplayList.cons : (alpha : Sort u) -> alpha -> ReplayList alpha -> ReplayList alpha`.
fn build_parameterized_inductive_replay_shard() -> ShardReader {
    let mut writer = ShardWriter::new();
    let u_name = writer.add_string("u");
    let l_u = writer.add_level(FlatLevel::param(u_name));
    let sort_u = writer.add_expr(FlatExpr::sort(l_u));
    let levels_u = writer.add_level_list(&[l_u]);

    let ind_name = writer.add_string("ReplayList");
    let nil_name = writer.add_string("ReplayList.nil");
    let cons_name = writer.add_string("ReplayList.cons");

    let replay_list = writer.add_expr(FlatExpr::const_ref(ind_name, levels_u));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    let bvar1 = writer.add_expr(FlatExpr::bvar(1));
    let bvar2 = writer.add_expr(FlatExpr::bvar(2));

    let ind_type = writer.add_expr(FlatExpr::pi(0, sort_u, sort_u));
    let nil_return = writer.add_expr(FlatExpr::app(replay_list, bvar0));
    let nil_type = writer.add_expr(FlatExpr::pi(0, sort_u, nil_return));
    let cons_tail = writer.add_expr(FlatExpr::app(replay_list, bvar1));
    let cons_return = writer.add_expr(FlatExpr::app(replay_list, bvar2));
    let cons_tail_to_return = writer.add_expr(FlatExpr::pi(0, cons_tail, cons_return));
    let cons_head_to_tail = writer.add_expr(FlatExpr::pi(0, bvar0, cons_tail_to_return));
    let cons_type = writer.add_expr(FlatExpr::pi(0, sort_u, cons_head_to_tail));

    let mut ind_header = MathverseConstantHeader {
        name_idx: ind_name,
        type_idx: ind_type,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Inductive as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: u_name,
        level_params_count: 1,
        _pad2: [0u8; 26],
    };
    ind_header.set_inductive_decl_num_params(1);
    writer.add_constant(ind_header);
    writer.add_constant(MathverseConstantHeader {
        name_idx: nil_name,
        type_idx: nil_type,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Constructor as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: u_name,
        level_params_count: 1,
        _pad2: [0u8; 26],
    });
    writer.add_constant(MathverseConstantHeader {
        name_idx: cons_name,
        type_idx: cons_type,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Constructor as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: u_name,
        level_params_count: 1,
        _pad2: [0u8; 26],
    });

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

fn add_inductive_family_constant(
    writer: &mut ShardWriter,
    name_idx: u32,
    type_idx: u32,
    decl_kind: DeclKind,
    import_confidence: ImportConfidence,
    axiom_profile: AxiomProfile,
) {
    writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: import_confidence as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: decl_kind as u8,
        axiom_profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
}

fn finish_test_shard(writer: ShardWriter) -> ShardReader {
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

/// Build a parameterized-or-indexed family skeleton:
/// `ParamOrIndexed : Type -> Type`,
/// `ParamOrIndexed.mk : (A : Type) -> A -> ParamOrIndexed A`.
///
/// Without populated `InductiveDecl.num_params` shard metadata, this shard
/// cannot distinguish the parameter/index boundary needed by checked
/// `add_inductive()` replay.
fn build_parameterized_or_indexed_inductive_shard(
    import_confidence: ImportConfidence,
    axiom_profile: AxiomProfile,
) -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let l1 = writer.add_level(FlatLevel::succ(l0));
    let sort_type = writer.add_expr(FlatExpr::sort(l1));

    let ind_name = writer.add_string("ParamOrIndexed");
    let ctor_name = writer.add_string("ParamOrIndexed.mk");

    let ind_ref = writer.add_expr(FlatExpr::const_ref(ind_name, u32::MAX));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    let bvar1 = writer.add_expr(FlatExpr::bvar(1));
    let ind_bvar1 = writer.add_expr(FlatExpr::app(ind_ref, bvar1));
    let ctor_tail = writer.add_expr(FlatExpr::pi(0, bvar0, ind_bvar1));
    let ctor_type = writer.add_expr(FlatExpr::pi(0, sort_type, ctor_tail));
    let ind_type = writer.add_expr(FlatExpr::pi(0, sort_type, sort_type));

    add_inductive_family_constant(
        &mut writer,
        ind_name,
        ind_type,
        DeclKind::Inductive,
        import_confidence,
        axiom_profile,
    );
    add_inductive_family_constant(
        &mut writer,
        ctor_name,
        ctor_type,
        DeclKind::Constructor,
        import_confidence,
        axiom_profile,
    );

    finish_test_shard(writer)
}

/// Build a same-shard mutual block skeleton:
/// `MutualEven : Type`, `MutualOdd : Type`,
/// `MutualEven.succOdd : MutualOdd -> MutualEven`,
/// `MutualOdd.succEven : MutualEven -> MutualOdd`.
///
/// By default, the inductive headers carry `InductiveVal.all_names` metadata
/// so checked replay can rebuild the full `InductiveDecl.types` block.
fn build_mutual_inductive_skeleton_shard(
    import_confidence: ImportConfidence,
    axiom_profile: AxiomProfile,
) -> ShardReader {
    build_mutual_inductive_skeleton_shard_with_all_names_metadata(
        import_confidence,
        axiom_profile,
        true,
    )
}

fn build_mutual_inductive_skeleton_shard_with_all_names_metadata(
    import_confidence: ImportConfidence,
    axiom_profile: AxiomProfile,
    with_all_names_metadata: bool,
) -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let l1 = writer.add_level(FlatLevel::succ(l0));
    let sort_type = writer.add_expr(FlatExpr::sort(l1));

    let even_name = writer.add_string("MutualEven");
    let odd_name = writer.add_string("MutualOdd");
    let even_zero_name = writer.add_string("MutualEven.zero");
    let even_succ_name = writer.add_string("MutualEven.succOdd");
    let odd_succ_name = writer.add_string("MutualOdd.succEven");

    let even_ref = writer.add_expr(FlatExpr::const_ref(even_name, u32::MAX));
    let odd_ref = writer.add_expr(FlatExpr::const_ref(odd_name, u32::MAX));
    let even_succ_type = writer.add_expr(FlatExpr::pi(0, odd_ref, even_ref));
    let odd_succ_type = writer.add_expr(FlatExpr::pi(0, even_ref, odd_ref));
    let all_names_block = with_all_names_metadata.then(|| {
        let start = writer.add_string_block(&["MutualEven", "MutualOdd"]);
        (start, 2u16)
    });

    for name_idx in [even_name, odd_name] {
        let mut header = MathverseConstantHeader {
            name_idx,
            type_idx: sort_type,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: import_confidence as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Inductive as u8,
            axiom_profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };
        header.set_inductive_decl_num_params(0);
        if let Some((start, count)) = all_names_block {
            header.set_inductive_decl_all_names(start, count);
        }
        writer.add_constant(header);
    }
    add_inductive_family_constant(
        &mut writer,
        even_zero_name,
        even_ref,
        DeclKind::Constructor,
        import_confidence,
        axiom_profile,
    );
    add_inductive_family_constant(
        &mut writer,
        even_succ_name,
        even_succ_type,
        DeclKind::Constructor,
        import_confidence,
        axiom_profile,
    );
    add_inductive_family_constant(
        &mut writer,
        odd_succ_name,
        odd_succ_type,
        DeclKind::Constructor,
        import_confidence,
        axiom_profile,
    );

    finish_test_shard(writer)
}

/// Build a simple family plus an imported recursor skeleton whose type does
/// not match the recursor generated by checked replay. This documents the
/// current boundary: shard headers lack `RecursorVal.rules` and `arg_order`
/// metadata for reconciling imported recursor constants.
fn build_recursor_arg_order_skeleton_shard(
    import_confidence: ImportConfidence,
    axiom_profile: AxiomProfile,
) -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let l1 = writer.add_level(FlatLevel::succ(l0));
    let sort_type = writer.add_expr(FlatExpr::sort(l1));

    let ind_name = writer.add_string("ArgOrderNat");
    let zero_name = writer.add_string("ArgOrderNat.zero");
    let succ_name = writer.add_string("ArgOrderNat.succ");
    let rec_on_name = writer.add_string("ArgOrderNat.recOn");

    let ind_ref = writer.add_expr(FlatExpr::const_ref(ind_name, u32::MAX));
    let succ_type = writer.add_expr(FlatExpr::pi(0, ind_ref, ind_ref));

    add_inductive_family_constant(
        &mut writer,
        ind_name,
        sort_type,
        DeclKind::Inductive,
        import_confidence,
        axiom_profile,
    );
    add_inductive_family_constant(
        &mut writer,
        zero_name,
        ind_ref,
        DeclKind::Constructor,
        import_confidence,
        axiom_profile,
    );
    add_inductive_family_constant(
        &mut writer,
        succ_name,
        succ_type,
        DeclKind::Constructor,
        import_confidence,
        axiom_profile,
    );
    add_inductive_family_constant(
        &mut writer,
        rec_on_name,
        sort_type,
        DeclKind::Recursor,
        import_confidence,
        axiom_profile,
    );

    finish_test_shard(writer)
}

/// Build a shard where a changed SCC sits between a seed prerequisite and a
/// downstream dependent:
/// `Seed`, `CycleA -> Seed, CycleB`, `CycleB -> CycleA`, `Downstream -> CycleA`.
fn build_scc_boundary_shard() -> ShardReader {
    build_test_shard(&[
        ("Seed", &[]),
        ("CycleA", &["Seed", "CycleB"]),
        ("CycleB", &["CycleA"]),
        ("Downstream", &["CycleA"]),
    ])
}

#[test]
fn test_build_dependency_graph_chain() {
    let reader = build_test_shard(&[("A", &[]), ("B", &["A"]), ("C", &["B"])]);
    let deps = build_dependency_graph(&reader);

    assert!(deps["A"].is_empty());
    assert!(deps["B"].contains("A"));
    assert!(deps["C"].contains("B"));
}

#[test]
fn test_topological_sort_chain() {
    let reader = build_test_shard(&[("A", &[]), ("B", &["A"]), ("C", &["B"])]);
    let deps = build_dependency_graph(&reader);
    let topo = topological_sort(&deps);

    assert!(topo.cyclic.is_empty(), "no cycles expected");
    assert_eq!(topo.order.len(), 3);

    let pos_a = topo.order.iter().position(|n| n == "A").unwrap();
    let pos_b = topo.order.iter().position(|n| n == "B").unwrap();
    let pos_c = topo.order.iter().position(|n| n == "C").unwrap();
    assert!(pos_a < pos_b, "A must precede B");
    assert!(pos_b < pos_c, "B must precede C");
}

#[test]
fn test_topological_sort_cycle_detection() {
    let mut deps: HashMap<String, HashSet<String>> = HashMap::new();
    deps.insert("X".to_string(), HashSet::from(["Y".to_string()]));
    deps.insert("Y".to_string(), HashSet::from(["X".to_string()]));
    deps.insert("Z".to_string(), HashSet::new());

    let topo = topological_sort(&deps);

    assert_eq!(topo.cyclic.len(), 2, "X and Y form a cycle");
    assert!(topo.cyclic.contains(&"X".to_string()));
    assert!(topo.cyclic.contains(&"Y".to_string()));
    assert_eq!(topo.order.len(), 1, "only Z is non-cyclic");
    assert_eq!(topo.order[0], "Z");
}

#[test]
fn test_verify_shard_incremental_chain() {
    let reader = build_test_shard(&[("A", &[]), ("B", &["A"]), ("C", &["B"])]);
    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 3);
    assert_eq!(report.cycle_skipped, 0);
    // `build_test_shard` emits decl_kind 0 (Theorem). "A" has no value; "B" and
    // "C" carry a synthetic Const-chain value that the kernel does NOT accept as
    // a well-typed theorem body. Every constant therefore falls back to an axiom
    // (AxiomFallback) so dependents still resolve — but NONE is a genuine
    // proof-check. This is exactly the overcount this change removes: the old
    // verifier stamped all three KernelVerified.
    assert_eq!(
        report.kernel_verified, 0,
        "synthetic theorem bodies do not genuinely kernel-verify: failures = {:?}",
        report.failures
    );
    assert_eq!(report.axiom_accepted, 0);
    assert_eq!(
        report.axiom_fallback, 3,
        "all three fall back to an axiom: failures = {:?}",
        report.failures
    );
    // B and C HAD a value the kernel rejected (masked failure); A had none.
    assert_eq!(
        report.axiom_fallback_names.len(),
        2,
        "B and C carried values that failed to typecheck: {:?}",
        report.axiom_fallback_names
    );
    assert!(
        report
            .axiom_fallback_names
            .iter()
            .any(|(name, _)| name == "B"),
        "B's masked typecheck failure must be recorded: {:?}",
        report.axiom_fallback_names
    );
    assert_eq!(report.failed, 0);
}

#[test]
fn test_verify_shard_incremental_definition_chain() {
    let reader = build_valid_definition_chain_shard();
    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 3);
    // P is a NO_VALUE axiom (AxiomAccepted); idP and applyId are value-bearing
    // Definitions that genuinely typecheck (KernelVerified).
    assert_eq!(
        report.kernel_verified, 2,
        "the 2 value-bearing definitions should genuinely kernel-verify: failures = {:?}",
        report.failures
    );
    assert_eq!(
        report.axiom_accepted, 1,
        "the NO_VALUE axiom P is accepted, not proof-checked: failures = {:?}",
        report.failures
    );
    assert_eq!(report.axiom_fallback, 0);
    assert_eq!(report.failed, 0);
    assert_eq!(report.seeded_checked, 0);
    assert_eq!(report.seeded_unchecked, 0);
}

#[test]
fn test_fresh_env_per_constant_fails_for_deps() {
    let reader = build_test_shard(&[("A", &[]), ("B", &["A"]), ("C", &["B"])]);

    let mut isolated_pass = 0;
    for constant in &reader.constants {
        let name = reader
            .strings
            .get(constant.name_idx as usize)
            .cloned()
            .unwrap_or_default();
        let type_expr = match reconstruct_from_shard_with_level_lists(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            &reader.level_lists,
            constant.type_idx,
        ) {
            Ok(e) => e,
            Err(_) => continue,
        };
        let mut env = Environment::new();
        let decl = Declaration::Axiom {
            name: Name::from_string(&name),
            level_params: vec![],
            type_: type_expr,
        };
        if env.add_decl(decl).is_ok() {
            isolated_pass += 1;
        }
    }

    let report = verify_shard_incremental(&reader);
    // The fresh-per-constant loop registers each constant's TYPE as a standalone
    // axiom, so it counts every type-well-formed constant. The incremental path
    // splits its successes across genuine proof-checks (kernel_verified) and
    // axiom registrations (axiom_accepted + axiom_fallback); their sum is the
    // honest count of constants it successfully registered.
    let registered = report.kernel_verified + report.axiom_accepted + report.axiom_fallback;
    assert!(
        registered >= isolated_pass,
        "incremental ({registered}) should register >= fresh-per-constant ({isolated_pass})",
    );
}

#[test]
fn test_verify_incremental_empty_shard() {
    let mut w = ShardWriter::new();
    let _ = w.add_level(FlatLevel::zero());
    let mut buf = Vec::new();
    w.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    let report = verify_shard_incremental(&reader);
    assert_eq!(report.total, 0);
    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.failed, 0);
    assert_eq!(report.cycle_skipped, 0);
}

#[test]
fn test_verify_incremental_report_elapsed() {
    let reader = build_test_shard(&[("X", &[])]);
    let report = verify_shard_incremental(&reader);
    assert!(report.elapsed_secs >= 0.0);
    assert!(report.elapsed_secs < 60.0);
}

#[test]
fn test_dependency_graph_self_reference_removed() {
    let reader = build_test_shard(&[("Self", &["Self"])]);
    let deps = build_dependency_graph(&reader);
    assert!(
        !deps["Self"].contains("Self"),
        "self-reference should be removed"
    );
}

#[test]
fn test_dependency_graph_external_deps_ignored_in_topo() {
    let reader = build_test_shard(&[("A", &[]), ("B", &["A", "External"])]);
    let deps = build_dependency_graph(&reader);
    let topo = topological_sort(&deps);

    assert!(topo.cyclic.is_empty());
    assert_eq!(topo.order.len(), 2);
}

#[test]
fn test_plan_incremental_recheck_selects_dependents_and_prereqs() {
    let reader = build_valid_definition_chain_shard();
    let plan = plan_incremental_recheck(&reader, ["idP"]);

    assert_eq!(plan.requested, vec!["idP"]);
    assert!(plan.missing.is_empty());
    assert_eq!(plan.seed_order, vec!["P"]);
    assert!(plan.seed_cyclic.is_empty());
    assert_eq!(plan.recheck_order, vec!["idP", "applyId"]);
    assert!(plan.cycle_skipped.is_empty());
}

#[test]
fn test_verify_shard_incremental_recheck_only_affected_slice() {
    let reader = build_valid_definition_chain_shard();
    let report = verify_shard_incremental_recheck(&reader, ["idP"]);

    assert_eq!(report.total, 2);
    assert_eq!(report.seeded_checked, 1, "P should be seeded via add_decl");
    assert_eq!(
        report.seeded_unchecked, 0,
        "acyclic non-inductive prerequisites should not use unchecked seeding"
    );
    assert_eq!(
        report.kernel_verified, 2,
        "only changed definition and downstream dependent should be rechecked: failures = {:?}",
        report.failures
    );
    assert_eq!(report.failed, 0);
    assert_eq!(report.cycle_skipped, 0);
}

#[test]
fn test_plan_incremental_recheck_missing_constant() {
    let reader = build_valid_definition_chain_shard();
    let plan = plan_incremental_recheck(&reader, ["Missing", "P"]);

    assert_eq!(plan.requested, vec!["P"]);
    assert_eq!(plan.missing, vec!["Missing"]);
    assert!(plan.seed_order.is_empty());
    assert_eq!(plan.recheck_order, vec!["P", "idP", "applyId"]);
}

#[test]
fn test_plan_incremental_recheck_scc_boundary_keeps_changed_cycle_out_of_seed_set() {
    let reader = build_scc_boundary_shard();
    let plan = plan_incremental_recheck(&reader, ["CycleB"]);

    assert_eq!(plan.requested, vec!["CycleB"]);
    assert_eq!(plan.seed_order, vec!["Seed"]);
    assert!(plan.seed_cyclic.is_empty());
    assert!(
        !plan
            .seed_order
            .iter()
            .any(|name| name == "CycleA" || name == "CycleB"),
        "mixed changed/unchanged SCC members must not be seeded as prerequisites"
    );
    assert!(
        !plan
            .seed_cyclic
            .iter()
            .any(|name| name == "CycleA" || name == "CycleB"),
        "mixed changed/unchanged SCC members must stay on the recheck side"
    );
    assert!(
        plan.cycle_skipped.contains(&"CycleA".to_string()),
        "unchanged SCC peer should be treated as part of the changed recheck slice"
    );
    assert!(
        plan.cycle_skipped.contains(&"CycleB".to_string()),
        "changed SCC member should remain in the recheck cycle set"
    );
}

#[test]
fn test_verify_shard_incremental_recheck_scc_boundary_only_seeds_true_prereqs() {
    let reader = build_scc_boundary_shard();
    let report = verify_shard_incremental_recheck(&reader, ["CycleB"]);

    assert_eq!(report.total, 3);
    assert_eq!(
        report.seeded_checked, 1,
        "only the acyclic prerequisite should be seeded through checked replay"
    );
    assert_eq!(
        report.seeded_unchecked, 0,
        "acyclic non-inductive prerequisites should not use unchecked seeding"
    );
    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.cycle_skipped, 3);
    assert!(report
        .failures
        .iter()
        .any(|(name, msg)| name == "CycleA" && msg == "dependency cycle"));
    assert!(report
        .failures
        .iter()
        .any(|(name, msg)| name == "CycleB" && msg == "dependency cycle"));
}

/// Build a shard with a universe-polymorphic constant (non-empty level_params).
///
/// Creates a constant whose type is `Sort(u)` where `u` is a universe parameter,
/// and `level_params = ["u"]`. This exercises the level_lists and level_params
/// reconstruction paths.
#[test]
fn test_verify_incremental_polymorphic_level_params() {
    let mut writer = ShardWriter::new();

    // Add the universe parameter name "u" to the string table.
    let u_str_idx = writer.add_string("u");
    let name_idx = writer.add_string("Poly.id");

    // Build a level: Level.param("u")
    let l_param = writer.add_level(FlatLevel::param(u_str_idx));
    // Build a level list containing [l_param]
    let _level_list_offset = writer.add_level_list(&[l_param]);

    // Type = Sort(u)
    let sort_u = writer.add_expr(FlatExpr::sort(l_param));

    // Value = a const reference to itself with the level_list (not meaningful
    // semantically, but exercises the reconstruction path).
    // Actually, use a simple identity: the value is Sort(u) too (like an axiom).
    // For a proper theorem, type and value need to type-check. Let's make it
    // an axiom (no value) so the kernel just checks the type is well-formed.

    // The level_params_start is the string table index where consecutive
    // level param names start. "u" was added at u_str_idx.
    writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx: sort_u,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Axiom as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: u_str_idx,
        level_params_count: 1,
        _pad2: [0u8; 26],
    });

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 1);
    // A NO_VALUE polymorphic axiom: the kernel checks its type is well-formed but
    // there is no proof term, so it is AxiomAccepted, not KernelVerified.
    assert_eq!(
        report.axiom_accepted, 1,
        "polymorphic axiom with level_params=[u] should be axiom-accepted: failures = {:?}",
        report.failures
    );
    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.failed, 0);
    assert_eq!(report.inductive_registered, 0);
}

/// Build a malformed inductive-family skeleton and verify it fails closed
/// when checked replay metadata is unavailable.
#[test]
fn test_verify_incremental_inductive_skeleton_without_replay_metadata_fails_closed() {
    let mut writer = ShardWriter::new();

    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let ind_name_idx = writer.add_string("MyInd");
    let ctor_name_idx = writer.add_string("MyInd.mk");
    let rec_name_idx = writer.add_string("MyInd.rec");

    // Inductive type
    writer.add_constant(MathverseConstantHeader {
        name_idx: ind_name_idx,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Inductive as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    // Constructor
    writer.add_constant(MathverseConstantHeader {
        name_idx: ctor_name_idx,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Constructor as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    // Recursor
    writer.add_constant(MathverseConstantHeader {
        name_idx: rec_name_idx,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Recursor as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 3);
    assert_eq!(report.inductive_registered, 0);
    assert_eq!(
        report.kernel_verified, 0,
        "no kernel-verified expected for unreplayable inductive skeletons"
    );
    // MyInd / MyInd.mk: the unreplayable skeleton downgrades to kernel-checked
    // STAND-IN axioms of the stated types (clean fallback lane, no taint).
    // MyInd.rec: recursor rows are never stand-in eligible (an elimination
    // principle is real logical strength) and keep failing closed.
    assert_eq!(
        report.axiom_fallback, 2,
        "family root + constructor stand-ins expected; failures = {:?}",
        report.failures
    );
    assert_eq!(report.family_standins.len(), 2);
    assert_eq!(report.failed, 1, "failures = {:?}", report.failures);
    assert!(report
        .failures
        .iter()
        .all(|(name, msg)| name == "MyInd.rec" && msg.contains("checked add_inductive replay")));
    assert_eq!(report.reconstruct_failed, 0);
}

#[test]
fn test_verify_incremental_simple_inductive_replayed_checked() {
    let reader = build_simple_inductive_replay_shard();
    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 3);
    assert_eq!(
        report.kernel_verified, 3,
        "inductive and constructors should route through checked add_inductive replay: failures = {:?}",
        report.failures
    );
    assert_eq!(
        report.inductive_registered, 0,
        "simple zero-parameter inductive family should avoid unchecked skeleton registration"
    );
    assert_eq!(report.failed, 0);
    assert_eq!(report.reconstruct_failed, 0);
}

/// Build two structure-shaped single-constructor inductives where the second's
/// constructor FIELD references the first (mirroring Lean's
/// `AddSemigroup` <- `AddMonoid.mk` parent-class field). The constants are
/// written in an order (Derived first) that, without folding constructor-field
/// deps into the inductive root, lets the topological sort place `DerivedStruct`
/// before `BaseStruct`, so the atomic `add_inductive(DerivedStruct)` would fail
/// with `Unknown constant: BaseStruct`.
///
/// - `BaseStruct : Type`, `BaseStruct.mk : BaseStruct`
/// - `DerivedStruct : Type`, `DerivedStruct.mk : BaseStruct -> DerivedStruct`
fn build_structure_field_dependency_shard() -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let l1 = writer.add_level(FlatLevel::succ(l0));
    let sort_type = writer.add_expr(FlatExpr::sort(l1));

    let base_name = writer.add_string("BaseStruct");
    let base_mk = writer.add_string("BaseStruct.mk");
    let derived_name = writer.add_string("DerivedStruct");
    let derived_mk = writer.add_string("DerivedStruct.mk");

    let base_ref = writer.add_expr(FlatExpr::const_ref(base_name, u32::MAX));
    let derived_ref = writer.add_expr(FlatExpr::const_ref(derived_name, u32::MAX));
    // DerivedStruct.mk : BaseStruct -> DerivedStruct
    let derived_mk_type = writer.add_expr(FlatExpr::pi(0, base_ref, derived_ref));

    let inductive = |name_idx, type_idx, mut h: MathverseConstantHeader| {
        h.name_idx = name_idx;
        h.type_idx = type_idx;
        h.decl_kind = DeclKind::Inductive as u8;
        h
    };
    let base_template = MathverseConstantHeader {
        name_idx: 0,
        type_idx: 0,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Inductive as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };

    // Intentionally write DerivedStruct (+ ctor) BEFORE BaseStruct so the bug
    // would surface absent the dependency fold.
    let mut derived_ind = inductive(derived_name, sort_type, base_template);
    derived_ind.set_inductive_decl_num_params(0);
    writer.add_constant(derived_ind);
    let mut derived_ctor = base_template;
    derived_ctor.name_idx = derived_mk;
    derived_ctor.type_idx = derived_mk_type;
    derived_ctor.decl_kind = DeclKind::Constructor as u8;
    writer.add_constant(derived_ctor);

    let mut base_ind = inductive(base_name, sort_type, base_template);
    base_ind.set_inductive_decl_num_params(0);
    writer.add_constant(base_ind);
    let mut base_ctor = base_template;
    base_ctor.name_idx = base_mk;
    base_ctor.type_idx = base_ref;
    base_ctor.decl_kind = DeclKind::Constructor as u8;
    writer.add_constant(base_ctor);

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

#[test]
fn test_build_dependency_graph_folds_constructor_field_deps_into_inductive_root() {
    let reader = build_structure_field_dependency_shard();
    let deps = build_dependency_graph(&reader);

    // The DerivedStruct inductive's TYPE is just `Type`, with no reference to
    // BaseStruct; only DerivedStruct.mk's field references it. After folding,
    // the inductive root must depend on BaseStruct so it is ordered after it.
    let derived_deps = deps
        .get("DerivedStruct")
        .expect("DerivedStruct present in dep graph");
    assert!(
        derived_deps.contains("BaseStruct"),
        "constructor-field dependency BaseStruct must be folded into the DerivedStruct \
         inductive root's deps so add_inductive runs with its field deps present; got {derived_deps:?}"
    );
    // The fold must NOT introduce a self-edge (DerivedStruct.mk returns
    // DerivedStruct) — that would create a cycle the topo sort drops.
    assert!(
        !derived_deps.contains("DerivedStruct"),
        "the family's own member names must be excluded from the folded set"
    );
}

#[test]
fn test_verify_incremental_structure_field_dependency_orders_and_registers() {
    let reader = build_structure_field_dependency_shard();
    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 4);
    assert_eq!(
        report.kernel_verified, 4,
        "both structures must replay through checked add_inductive once the \
         constructor-field dependency is ordered first: failures = {:?}",
        report.failures
    );
    assert_eq!(report.failed, 0, "no Unknown-constant ordering failures");
    assert_eq!(report.reconstruct_failed, 0);
}

#[test]
fn test_verify_incremental_inductive_replay_metadata_infers_constructor_groups() {
    let reader = build_simple_inductive_replay_shard();
    let ind_header = reader
        .constants
        .iter()
        .find(|constant| {
            reader
                .strings
                .get(constant.name_idx as usize)
                .map(String::as_str)
                == Some("ReplayNat")
        })
        .unwrap();
    let reconstructed = super::reconstruct_constant("ReplayNat", &reader, ind_header).unwrap();
    let metadata =
        super::build_single_type_inductive_replay_metadata(&reader, ind_header, &reconstructed)
            .unwrap()
            .unwrap();

    assert_eq!(metadata.decl.num_params, 0);
    assert_eq!(metadata.decl.types.len(), 1);
    assert_eq!(metadata.decl.types[0].name, Name::from_string("ReplayNat"));
    assert_eq!(metadata.decl.types[0].constructors.len(), 2);
    assert_eq!(
        metadata.decl.types[0].constructors[0].name,
        Name::from_string("ReplayNat.zero")
    );
    assert_eq!(
        metadata.decl.types[0].constructors[1].name,
        Name::from_string("ReplayNat.succ")
    );
    assert!(metadata
        .generated_names
        .contains(&Name::from_string("ReplayNat.rec")));
}

#[test]
fn test_verify_incremental_parameterized_inductive_replayed_checked_from_num_params_metadata() {
    let reader = build_parameterized_inductive_replay_shard();
    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 3);
    assert_eq!(
        report.kernel_verified, 3,
        "parameterized inductive family should replay through checked add_inductive: failures = {:?}",
        report.failures
    );
    assert_eq!(
        report.inductive_registered, 0,
        "InductiveDecl.num_params metadata should avoid unchecked skeleton registration"
    );
    assert_eq!(report.failed, 0);
}

#[test]
fn test_verify_incremental_inductive_replay_uses_num_params_metadata() {
    let reader = build_parameterized_inductive_replay_shard();
    let ind_header = reader
        .constants
        .iter()
        .find(|constant| {
            reader
                .strings
                .get(constant.name_idx as usize)
                .map(String::as_str)
                == Some("ReplayList")
        })
        .unwrap();
    let reconstructed = super::reconstruct_constant("ReplayList", &reader, ind_header).unwrap();
    let metadata =
        super::build_single_type_inductive_replay_metadata(&reader, ind_header, &reconstructed)
            .unwrap()
            .unwrap();

    assert_eq!(ind_header.inductive_decl_num_params(), Some(1));
    assert_eq!(metadata.decl.num_params, 1);
    assert_eq!(metadata.decl.types.len(), 1);
    assert_eq!(metadata.decl.types[0].constructors.len(), 2);
}

/// Regenerate the `ReplayNat` family through Clean's own checked
/// `add_inductive` on a fresh `Environment::new()` — the SAME base env the
/// per-shard verifier uses (`verify_shard_incremental`) — so the recursor a
/// test extracts is byte-for-byte the one the production replay compares the
/// shard copy against.
fn replaynat_scratch_env() -> Environment {
    let base = build_simple_inductive_replay_shard();
    let ind_header = base
        .constants
        .iter()
        .find(|constant| {
            base.strings
                .get(constant.name_idx as usize)
                .map(String::as_str)
                == Some("ReplayNat")
        })
        .expect("ReplayNat header present");
    let reconstructed = super::reconstruct_constant("ReplayNat", &base, ind_header).unwrap();
    let metadata =
        super::build_single_type_inductive_replay_metadata(&base, ind_header, &reconstructed)
            .unwrap()
            .unwrap();
    let mut scratch = Environment::new();
    scratch
        .add_inductive(metadata.decl)
        .expect("ReplayNat family replays through checked add_inductive");
    scratch
}

/// Build the `ReplayNat` family (`ReplayNat : Type`, `.zero`, `.succ`) PLUS a
/// shard-shipped `ReplayNat.rec` whose type is `rec_type` and whose level
/// params are `rec_level_params` (interned CONSECUTIVELY, as the header's
/// `(level_params_start, level_params_count)` span requires). Used to drive the
/// recursor accept/reject gate in `checked_inductive_replay_matches_shard`.
fn build_replaynat_shard_with_rec(rec_type: &Expr, rec_level_params: &[&str]) -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let l1 = writer.add_level(FlatLevel::succ(l0));
    let sort_type = writer.add_expr(FlatExpr::sort(l1));

    let ind_name = writer.add_string("ReplayNat");
    let zero_name = writer.add_string("ReplayNat.zero");
    let succ_name = writer.add_string("ReplayNat.succ");
    let rec_name = writer.add_string("ReplayNat.rec");

    let replay_nat = writer.add_expr(FlatExpr::const_ref(ind_name, u32::MAX));
    let succ_type = writer.add_expr(FlatExpr::pi(0, replay_nat, replay_nat));

    // Intern the recursor's level-param names CONSECUTIVELY *before* lowering
    // the recursor type: the header encodes level params as a span of
    // consecutive interned string indices, and lowering only ever dedups
    // already-interned names (never inserts a name between these two).
    let (lp_start, lp_count) = if rec_level_params.is_empty() {
        (0u32, 0u16)
    } else {
        let start = writer.add_string(rec_level_params[0]);
        for name in &rec_level_params[1..] {
            writer.add_string(name);
        }
        (start, rec_level_params.len() as u16)
    };
    let rec_type_idx = crate::hol::opentheory_shard::lower_kernel_expr(rec_type, &mut writer);

    writer.add_constant(MathverseConstantHeader {
        name_idx: ind_name,
        type_idx: sort_type,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Inductive as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    writer.add_constant(MathverseConstantHeader {
        name_idx: zero_name,
        type_idx: replay_nat,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Constructor as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    writer.add_constant(MathverseConstantHeader {
        name_idx: succ_name,
        type_idx: succ_type,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Constructor as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    writer.add_constant(MathverseConstantHeader {
        name_idx: rec_name,
        type_idx: rec_type_idx,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Recursor as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: lp_start,
        level_params_count: lp_count,
        _pad2: [0u8; 26],
    });

    finish_test_shard(writer)
}

/// ACCEPT: a shard `.rec` that is definitionally equal to Clean's regenerated
/// recursor but STRUCTURALLY divergent — here via a renamed motive-universe
/// level param, the exact divergence class (a fresh motive-universe param NAME)
/// that made the real `Relation.ReflGen`/`TransGen`/`ReflTransGen` families
/// fail. The OLD exact gate rejected it (`level_params !=`); the widened
/// `is_def_eq` recursor gate must accept it and count the whole family as
/// KernelVerified.
#[test]
fn test_verify_incremental_recursor_defeq_level_renamed_accepted() {
    let scratch = replaynat_scratch_env();
    let rec = scratch
        .get_const(&Name::from_string("ReplayNat.rec"))
        .expect("recursor regenerated by add_inductive")
        .clone();
    assert_eq!(
        rec.level_params.len(),
        1,
        "the monomorphic `Type` recursor carries exactly the motive-universe param"
    );

    // Rename the motive-universe param: definitionally identical, structurally
    // (and by exact `level_params`) different.
    let renamed = Name::from_string("MotiveUnivRenamed");
    let renamed_type = rec
        .type_
        .instantiate_level_params_direct(&rec.level_params, &[Level::param(renamed)]);
    let reader = build_replaynat_shard_with_rec(&renamed_type, &["MotiveUnivRenamed"]);

    let report = verify_shard_incremental(&reader);
    assert_eq!(report.total, 4);
    assert_eq!(
        report.kernel_verified, 4,
        "a def-eq (level-renamed) recursor must be accepted by the widened gate; failures = {:?}",
        report.failures
    );
    assert_eq!(report.failed, 0, "failures = {:?}", report.failures);
    assert_eq!(report.reconstruct_failed, 0);
}

/// REJECT (fail-closed): a shard `.rec` whose type is genuinely NOT def-eq to
/// the regenerated recursor (here the constructor type `ReplayNat -> ReplayNat`,
/// shipped with the recursor's 1-param arity so the gate reaches the
/// `is_def_eq` check rather than the arity check). The widened gate must still
/// reject the whole family — `is_def_eq` is exactly the kernel's equality, so a
/// forged/swapped recursor never slips through.
#[test]
fn test_verify_incremental_recursor_not_defeq_rejected() {
    let scratch = replaynat_scratch_env();
    let succ = scratch
        .get_const(&Name::from_string("ReplayNat.succ"))
        .expect("constructor regenerated by add_inductive")
        .clone();
    // `ReplayNat.succ : ReplayNat -> ReplayNat` is not the recursor type and is
    // not def-eq to it. Claim the recursor's 1-param arity to force the
    // is_def_eq comparison (not the arity short-circuit).
    let reader = build_replaynat_shard_with_rec(&succ.type_, &["MotiveUnivRenamed"]);

    let report = verify_shard_incremental(&reader);
    assert_eq!(report.total, 4);
    assert_eq!(
        report.kernel_verified, 0,
        "a non-def-eq recursor must fail the family closed; failures = {:?}",
        report.failures
    );
    // The forged recursor row itself is never installed (recursor rows are not
    // stand-in eligible); the root's superseded shard-match failure names the
    // member and the is_def_eq gate on the stand-in diagnostic lane.
    assert!(
        report
            .failures
            .iter()
            .any(|(name, _)| name == "ReplayNat.rec"),
        "the forged recursor row must fail closed; failures = {:?}",
        report.failures
    );
    assert!(
        report
            .family_standins
            .iter()
            .any(|(_, msg)| { msg.contains("ReplayNat.rec") && msg.contains("is_def_eq") }),
        "stand-in diagnostics must name the recursor member and the is_def_eq gate; \
         family_standins = {:?}",
        report.family_standins
    );
}

/// REJECT (fail-closed): a shard `.rec` that lies about its level-param arity
/// (Clean's recursor has one motive-universe param; this ships zero). The
/// widened gate's arity check is never relaxed, so the family fails closed.
#[test]
fn test_verify_incremental_recursor_level_arity_lie_rejected() {
    let scratch = replaynat_scratch_env();
    let rec = scratch
        .get_const(&Name::from_string("ReplayNat.rec"))
        .expect("recursor regenerated by add_inductive")
        .clone();
    // Ship the TRUE recursor type but declare zero level params.
    let reader = build_replaynat_shard_with_rec(&rec.type_, &[]);

    let report = verify_shard_incremental(&reader);
    assert_eq!(report.total, 4);
    assert_eq!(
        report.kernel_verified, 0,
        "a recursor arity lie must fail the family closed; failures = {:?}",
        report.failures
    );
    // As in the non-def-eq case: the lying recursor row fails closed and the
    // arity-mismatch detail surfaces on the stand-in diagnostic lane.
    assert!(
        report
            .failures
            .iter()
            .any(|(name, _)| name == "ReplayNat.rec"),
        "the lying recursor row must fail closed; failures = {:?}",
        report.failures
    );
    assert!(
        report
            .family_standins
            .iter()
            .any(|(_, msg)| { msg.contains("ReplayNat.rec") && msg.contains("arity") }),
        "stand-in diagnostics must name the recursor member and the arity mismatch; \
         family_standins = {:?}",
        report.family_standins
    );
}

#[test]
fn test_verify_incremental_inductive_trust_guard_rejects_weak_metadata() {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let unverified_name = writer.add_string("WeakInd");
    writer.add_constant(MathverseConstantHeader {
        name_idx: unverified_name,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::Unverified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Inductive as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    let axiomatized_name = writer.add_string("AxiomatizedInd");
    writer.add_constant(MathverseConstantHeader {
        name_idx: axiomatized_name,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Inductive as u8,
        axiom_profile: AxiomProfile::AXIOMATIZED,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 2);
    assert_eq!(report.inductive_registered, 0);
    assert_eq!(report.failed, 2);
    assert!(report.failures.iter().any(|(name, msg)| {
        name == "WeakInd" && msg.contains("requires KernelVerified confidence")
    }));
    assert!(report.failures.iter().any(|(name, msg)| {
        name == "AxiomatizedInd" && msg.contains("requires axiom-free metadata")
    }));
}

#[test]
fn test_verify_incremental_inductive_metadata_guard_documents_remaining_add_inductive_blocker() {
    assert_eq!(
        super::remaining_inductive_replay_metadata_fields(),
        &["RecursorVal rules/arg_order for imported recursor skeleton reconciliation"],
        "current shard metadata can rebuild simple mutual InductiveDecl groups; recursor metadata remains"
    );

    let header = MathverseConstantHeader {
        name_idx: 0,
        type_idx: 0,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Inductive as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };
    assert!(
        super::validate_inductive_skeleton_trust(&header).is_ok(),
        "trusted metadata may be considered only after KernelVerified, axiom-free guards pass"
    );
}

#[test]
fn test_verify_incremental_parameterized_or_indexed_family_without_num_params_downgrades_to_standins(
) {
    let reader = build_parameterized_or_indexed_inductive_shard(
        ImportConfidence::KernelVerified,
        AxiomProfile::NONE,
    );
    let ind_header = reader
        .constants
        .iter()
        .find(|constant| {
            reader
                .strings
                .get(constant.name_idx as usize)
                .map(String::as_str)
                == Some("ParamOrIndexed")
        })
        .unwrap();
    let reconstructed = super::reconstruct_constant("ParamOrIndexed", &reader, ind_header).unwrap();

    assert!(
        super::build_single_type_inductive_replay_metadata(&reader, ind_header, &reconstructed)
            .unwrap()
            .is_none(),
        "families with Pi binders need populated InductiveDecl.num_params metadata"
    );

    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 2);
    assert_eq!(report.inductive_registered, 0);
    // NEVER KernelVerified: the family did not replay. Both rows downgrade to
    // kernel-checked STAND-IN axioms of their stated types (clean fallback
    // lane) so downstream references resolve.
    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.failed, 0, "failures = {:?}", report.failures);
    assert_eq!(report.axiom_fallback, 2);
    assert_eq!(report.family_standins.len(), 2);
}

#[test]
fn test_verify_incremental_parameterized_or_indexed_family_fails_closed() {
    let reader = build_parameterized_or_indexed_inductive_shard(
        ImportConfidence::KernelVerified,
        AxiomProfile::AXIOMATIZED,
    );
    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 2);
    assert_eq!(report.inductive_registered, 0);
    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.failed, 2);
    assert!(report
        .failures
        .iter()
        .all(|(_, msg)| msg.contains("requires axiom-free metadata")));
}

#[test]
fn test_verify_incremental_mutual_inductive_without_all_names_downgrades_to_standins() {
    let reader = build_mutual_inductive_skeleton_shard_with_all_names_metadata(
        ImportConfidence::KernelVerified,
        AxiomProfile::NONE,
        false,
    );
    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 5);
    assert_eq!(report.inductive_registered, 0);
    // NEVER KernelVerified without the all_names metadata; every row
    // downgrades to a kernel-checked STAND-IN axiom of its stated type.
    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.failed, 0, "failures = {:?}", report.failures);
    assert_eq!(report.axiom_fallback, 5);
    assert_eq!(report.family_standins.len(), 5);
    assert_eq!(report.cycle_skipped, 0);
}

#[test]
fn test_verify_incremental_mutual_inductive_all_names_replayed_checked() {
    let reader =
        build_mutual_inductive_skeleton_shard(ImportConfidence::KernelVerified, AxiomProfile::NONE);
    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 5);
    assert_eq!(
        report.kernel_verified, 5,
        "metadata-backed mutual inductive family should replay through checked add_inductive: failures = {:?}",
        report.failures
    );
    assert_eq!(report.inductive_registered, 0);
    assert_eq!(report.failed, 0, "failures = {:?}", report.failures);
    assert_eq!(report.cycle_skipped, 0);
}

#[test]
fn test_verify_incremental_mutual_inductive_all_names_metadata_preserves_grouping() {
    let reader =
        build_mutual_inductive_skeleton_shard(ImportConfidence::KernelVerified, AxiomProfile::NONE);
    let even_header = reader
        .constants
        .iter()
        .find(|constant| {
            reader
                .strings
                .get(constant.name_idx as usize)
                .map(String::as_str)
                == Some("MutualEven")
        })
        .unwrap();
    let all_names = super::inductive_all_names_from_header(&reader, even_header)
        .unwrap()
        .unwrap();
    assert_eq!(
        all_names,
        vec![
            Name::from_string("MutualEven"),
            Name::from_string("MutualOdd")
        ]
    );

    let reconstructed = super::reconstruct_constant("MutualEven", &reader, even_header).unwrap();
    let metadata = super::build_inductive_replay_metadata(
        &reader,
        even_header,
        &reconstructed,
        crate::inductive_replay::NormMode::Shallow,
    )
    .unwrap()
    .unwrap();

    assert_eq!(metadata.decl.num_params, 0);
    assert_eq!(metadata.decl.types.len(), 2);
    assert_eq!(metadata.decl.types[0].name, Name::from_string("MutualEven"));
    assert_eq!(metadata.decl.types[0].constructors.len(), 2);
    assert_eq!(metadata.decl.types[1].name, Name::from_string("MutualOdd"));
    assert_eq!(metadata.decl.types[1].constructors.len(), 1);
    assert!(metadata
        .generated_names
        .contains(&Name::from_string("MutualOdd.rec")));
}

#[test]
fn test_verify_incremental_recursor_rules_arg_order_fails_closed_without_metadata() {
    let reader = build_recursor_arg_order_skeleton_shard(
        ImportConfidence::KernelVerified,
        AxiomProfile::NONE,
    );
    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 4);
    assert_eq!(report.inductive_registered, 0);
    // NEVER KernelVerified: the imported recursor skeleton cannot reconcile.
    // The root and constructors downgrade to kernel-checked STAND-IN axioms;
    // the RECURSOR row is never stand-in eligible and keeps failing closed.
    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.failed, 1, "failures = {:?}", report.failures);
    assert_eq!(report.axiom_fallback, 3);
    assert_eq!(report.family_standins.len(), 3);
    assert!(report.failures.iter().all(|(name, msg)| {
        name == "ArgOrderNat.recOn" && msg.contains("checked add_inductive replay")
    }));
}

#[test]
fn test_verify_incremental_recursor_rules_arg_order_fails_closed() {
    let reader =
        build_recursor_arg_order_skeleton_shard(ImportConfidence::Unverified, AxiomProfile::NONE);
    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 4);
    assert_eq!(report.inductive_registered, 0);
    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.failed, 4);
    assert!(report
        .failures
        .iter()
        .all(|(_, msg)| msg.contains("requires KernelVerified confidence")));
}

/// Build a family whose replay metadata reconstructs fine but whose checked
/// `add_inductive` replay the kernel must REJECT (non-positive occurrence):
/// `BadPos : Type`, `BadPos.mk : (BadPos -> BadPos) -> BadPos`.
fn build_nonpositive_inductive_replay_shard() -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let l1 = writer.add_level(FlatLevel::succ(l0));
    let sort_type = writer.add_expr(FlatExpr::sort(l1));

    let ind_name = writer.add_string("BadPos");
    let mk_name = writer.add_string("BadPos.mk");

    let bad_pos = writer.add_expr(FlatExpr::const_ref(ind_name, u32::MAX));
    let bad_to_bad = writer.add_expr(FlatExpr::pi(0, bad_pos, bad_pos));
    let mk_type = writer.add_expr(FlatExpr::pi(0, bad_to_bad, bad_pos));

    add_inductive_family_constant(
        &mut writer,
        ind_name,
        sort_type,
        DeclKind::Inductive,
        ImportConfidence::KernelVerified,
        AxiomProfile::NONE,
    );
    add_inductive_family_constant(
        &mut writer,
        mk_name,
        mk_type,
        DeclKind::Constructor,
        ImportConfidence::KernelVerified,
        AxiomProfile::NONE,
    );
    finish_test_shard(writer)
}

/// Build a kernel-valid `CorruptRecNat` family whose shard-stored
/// `CorruptRecNat.rec` TYPE is corrupted (`Prop` instead of the real recursor
/// type): metadata reconstruction and the scratch replay succeed, but the
/// member byte-match must fail on `CorruptRecNat.rec`.
fn build_corrupt_rec_inductive_replay_shard() -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let l1 = writer.add_level(FlatLevel::succ(l0));
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));
    let sort_type = writer.add_expr(FlatExpr::sort(l1));

    let ind_name = writer.add_string("CorruptRecNat");
    let zero_name = writer.add_string("CorruptRecNat.zero");
    let succ_name = writer.add_string("CorruptRecNat.succ");
    let rec_name = writer.add_string("CorruptRecNat.rec");

    let nat_ref = writer.add_expr(FlatExpr::const_ref(ind_name, u32::MAX));
    let succ_type = writer.add_expr(FlatExpr::pi(0, nat_ref, nat_ref));

    add_inductive_family_constant(
        &mut writer,
        ind_name,
        sort_type,
        DeclKind::Inductive,
        ImportConfidence::KernelVerified,
        AxiomProfile::NONE,
    );
    add_inductive_family_constant(
        &mut writer,
        zero_name,
        nat_ref,
        DeclKind::Constructor,
        ImportConfidence::KernelVerified,
        AxiomProfile::NONE,
    );
    add_inductive_family_constant(
        &mut writer,
        succ_name,
        succ_type,
        DeclKind::Constructor,
        ImportConfidence::KernelVerified,
        AxiomProfile::NONE,
    );
    // The corrupted recursor: stored type `Prop` can never match the
    // regenerated `CorruptRecNat.rec` type.
    add_inductive_family_constant(
        &mut writer,
        rec_name,
        sort_prop,
        DeclKind::Recursor,
        ImportConfidence::KernelVerified,
        AxiomProfile::NONE,
    );
    finish_test_shard(writer)
}

/// A2-2 family-replay diagnostics: a family the kernel's scratch
/// `add_inductive` REJECTS must record the scratch-rejection stage and the
/// real kernel error. The family downgrades to kernel-checked STAND-IN axioms
/// (never KernelVerified, no real inductive installed) and the stage marker
/// lands in the `family_standins` diagnostic lane.
#[test]
fn test_verify_incremental_family_scratch_rejection_surfaces_stage_and_kernel_error() {
    let reader = build_nonpositive_inductive_replay_shard();
    let report = verify_shard_incremental(&reader);

    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.failed, 0, "failures = {:?}", report.failures);
    assert_eq!(report.axiom_fallback, 2, "root + ctor stand-ins expected");
    let (_, root_msg) = report
        .family_standins
        .iter()
        .find(|(name, _)| name == "BadPos")
        .expect("BadPos stand-in should record the superseded replay failure");
    assert!(
        root_msg.contains("family replay failed at scratch add_inductive:"),
        "stand-in must carry the scratch-rejection stage marker, got: {root_msg}"
    );
}

/// The stand-in lever's point (phant-records): a dependent VALUE that only
/// references the failed family's NAME is genuinely kernel-checked against the
/// stand-in axiom and minted KernelVerified — and is NOT trust-withheld,
/// because a stand-in is a clean statement-only fallback, never a
/// masked-failure taint seed (measured motivation: `matrix.matrix.0` absent
/// chained 1,362 "Unknown constant" rejections).
#[test]
fn test_verify_incremental_family_standin_dependent_value_kernel_verified_untainted() {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let l1 = writer.add_level(FlatLevel::succ(l0));
    let sort_type = writer.add_expr(FlatExpr::sort(l1));

    let ind_name = writer.add_string("BadPos");
    let mk_name = writer.add_string("BadPos.mk");
    let dep_name = writer.add_string("BadPos.identity");

    let bad_pos = writer.add_expr(FlatExpr::const_ref(ind_name, u32::MAX));
    let bad_to_bad = writer.add_expr(FlatExpr::pi(0, bad_pos, bad_pos));
    let mk_type = writer.add_expr(FlatExpr::pi(0, bad_to_bad, bad_pos));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    let dep_value = writer.add_expr(FlatExpr::lam(0, bad_pos, bvar0));

    add_inductive_family_constant(
        &mut writer,
        ind_name,
        sort_type,
        DeclKind::Inductive,
        ImportConfidence::KernelVerified,
        AxiomProfile::NONE,
    );
    add_inductive_family_constant(
        &mut writer,
        mk_name,
        mk_type,
        DeclKind::Constructor,
        ImportConfidence::KernelVerified,
        AxiomProfile::NONE,
    );
    writer.add_constant(MathverseConstantHeader {
        name_idx: dep_name,
        type_idx: bad_to_bad,
        value_idx: dep_value,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Definition as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    let reader = finish_test_shard(writer);

    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 3);
    assert_eq!(
        report.axiom_fallback, 2,
        "BadPos + BadPos.mk downgrade to stand-ins; failures = {:?}",
        report.failures
    );
    assert_eq!(report.family_standins.len(), 2);
    assert_eq!(report.failed, 0, "failures = {:?}", report.failures);
    assert_eq!(
        report.kernel_verified, 1,
        "the dependent value must be genuinely kernel-checked against the \
         stand-in, not withheld; failures = {:?}",
        report.failures
    );
    assert_eq!(
        report.kernel_verified_names,
        vec!["BadPos.identity".to_string()],
        "the stand-ins themselves are never KernelVerified"
    );
}

/// A2-2 family-replay diagnostics: a corrupted shard-stored `rec` must record
/// the checked-replay shard-match stage AND name the mismatching member. The
/// root and constructors downgrade to kernel-checked STAND-IN axioms; the
/// corrupted RECURSOR row itself keeps failing closed (never stand-in
/// eligible), so the forged elimination principle is never installed.
#[test]
fn test_verify_incremental_family_shard_mismatch_surfaces_stage_and_member() {
    let reader = build_corrupt_rec_inductive_replay_shard();
    let report = verify_shard_incremental(&reader);

    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.failed, 1, "failures = {:?}", report.failures);
    assert_eq!(
        report.axiom_fallback, 3,
        "root + two ctor stand-ins expected"
    );
    assert!(
        report
            .failures
            .iter()
            .all(|(name, _)| name == "CorruptRecNat.rec"),
        "only the corrupted recursor row may fail; failures = {:?}",
        report.failures
    );
    let (_, root_msg) = report
        .family_standins
        .iter()
        .find(|(name, _)| name == "CorruptRecNat")
        .expect("CorruptRecNat stand-in should record the superseded replay failure");
    assert!(
        root_msg.contains(
            "family replay failed at checked-replay shard match: member CorruptRecNat.rec"
        ),
        "stand-in must carry the shard-mismatch stage marker and member, got: {root_msg}"
    );
}

/// A2-2 family-replay diagnostics: an unreconstructable family (no
/// `InductiveDecl.num_params` metadata) must record the metadata stage marker
/// (on the stand-in diagnostic lane since the family downgrades to
/// kernel-checked stand-in axioms).
#[test]
fn test_verify_incremental_family_metadata_unavailable_surfaces_stage() {
    let reader = build_parameterized_or_indexed_inductive_shard(
        ImportConfidence::KernelVerified,
        AxiomProfile::NONE,
    );
    let report = verify_shard_incremental(&reader);

    let (_, root_msg) = report
        .family_standins
        .iter()
        .find(|(name, _)| name == "ParamOrIndexed")
        .expect("ParamOrIndexed stand-in should record the superseded replay failure");
    assert!(
        root_msg.contains("family replay failed at metadata reconstruction"),
        "stand-in must carry the metadata-reconstruction stage marker, got: {root_msg}"
    );
}

/// A2-2 family-replay diagnostics: when the trust guard rejects the skeleton
/// (weak confidence), the message keeps the guard text AND the replay stage,
/// so the guard line no longer masks the real failure.
#[test]
fn test_verify_incremental_family_trust_guard_message_keeps_stage_suffix() {
    let reader = build_parameterized_or_indexed_inductive_shard(
        ImportConfidence::Unverified,
        AxiomProfile::NONE,
    );
    let report = verify_shard_incremental(&reader);

    let (_, root_msg) = report
        .failures
        .iter()
        .find(|(name, _)| name == "ParamOrIndexed")
        .expect("ParamOrIndexed root failure should be recorded");
    assert!(
        root_msg.contains("requires KernelVerified confidence"),
        "trust-guard rejection text must be unchanged, got: {root_msg}"
    );
    assert!(
        root_msg.contains("family replay failed at metadata reconstruction"),
        "trust-guard rejection must also carry the replay stage, got: {root_msg}"
    );
}

/// Test that a mixed shard with normal axioms, inductives, and polymorphic constants
/// all get counted correctly.
#[test]
fn test_verify_incremental_mixed_decl_kinds() {
    let mut writer = ShardWriter::new();

    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let axiom_name = writer.add_string("MyAxiom");
    let ind_name = writer.add_string("MyInd2");
    let thm_name = writer.add_string("MyThm");

    // A normal axiom (DeclKind::Axiom)
    writer.add_constant(MathverseConstantHeader {
        name_idx: axiom_name,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
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

    // An inductive
    writer.add_constant(MathverseConstantHeader {
        name_idx: ind_name,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Inductive as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    // A theorem (decl_kind=0 with no value → falls back to axiom path)
    writer.add_constant(MathverseConstantHeader {
        name_idx: thm_name,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Theorem as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 3);
    assert_eq!(report.inductive_registered, 0);
    // None of these are genuine proof-checks: MyAxiom (DeclKind::Axiom, NO_VALUE)
    // is AxiomAccepted; MyThm (DeclKind::Theorem, no value) falls back to an axiom
    // (AxiomFallback, no masked value); MyInd2 is an unreplayable inductive
    // skeleton that downgrades to a kernel-checked stand-in axiom.
    assert_eq!(
        report.kernel_verified, 0,
        "no value-bearing decls here, so nothing is genuinely kernel-verified: failures = {:?}",
        report.failures
    );
    assert_eq!(
        report.axiom_accepted, 1,
        "MyAxiom is a NO_VALUE axiom: failures = {:?}",
        report.failures
    );
    assert_eq!(
        report.axiom_fallback, 2,
        "MyThm (no value) falls back to an axiom and MyInd2 to a family \
         stand-in: failures = {:?}",
        report.failures
    );
    assert!(
        report.axiom_fallback_names.is_empty(),
        "MyThm carried no value, so it is not a masked failure"
    );
    assert_eq!(report.family_standins.len(), 1);
    assert_eq!(report.failed, 0, "failures = {:?}", report.failures);
}

// ---------------------------------------------------------------------------
// Cross-shard dependency resolution (the load-bearing proof)
// ---------------------------------------------------------------------------

/// Build shard A: a single axiom `CrossA : Type` (the cross-shard dependency).
///
/// `CrossA`'s type is `Sort 1` (= `Type 0`), so `CrossA` is itself a type and
/// can serve as the declared type of a constant in another shard.
fn build_cross_shard_a() -> ShardReader {
    let mut writer = ShardWriter::new();
    let name_a = writer.add_string("CrossA");

    // Sort 1 = Type 0: level = succ(zero).
    let l_zero = writer.add_level(FlatLevel::zero());
    let l_one = writer.add_level(FlatLevel::succ(l_zero));
    let type_a = writer.add_expr(FlatExpr::sort(l_one)); // CrossA : Type

    writer.add_constant(MathverseConstantHeader {
        name_idx: name_a,
        type_idx: type_a,
        value_idx: NO_VALUE,
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

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

/// Build shard B: a single axiom `CrossB : CrossA`, whose TYPE references the
/// constant `CrossA` defined in shard A.
///
/// Shard B carries the *string* "CrossA" (so the `Const` reference resolves a
/// name) but does NOT define the constant itself — that is the genuine
/// cross-shard dependency. Verifying B alone must fail to register `CrossB`,
/// because the kernel cannot type-check an axiom whose type mentions an unknown
/// constant.
fn build_cross_shard_b() -> ShardReader {
    let mut writer = ShardWriter::new();
    let name_b = writer.add_string("CrossB");
    let name_a = writer.add_string("CrossA");

    // CrossB's type is the bare reference `CrossA` (monomorphic: no level args).
    let type_b = writer.add_expr(FlatExpr::const_ref(name_a, u32::MAX));

    writer.add_constant(MathverseConstantHeader {
        name_idx: name_b,
        type_idx: type_b,
        value_idx: NO_VALUE,
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

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

/// The load-bearing proof: a constant in shard B whose type depends on a
/// constant defined in shard A FAILS per-shard but VERIFIES under the merged
/// corpus loader, because the merged library puts the dependency in-graph and
/// re-verifies the whole corpus in one prelude-seeded environment in global
/// topological order.
#[test]
fn test_cross_shard_dependency_resolved_by_corpus_verifier() {
    use super::verify_corpus_incremental;
    use crate::library::MathverseLibrary;
    use crate::trust::policy::TrustPolicy;

    let shard_a = build_cross_shard_a();
    let shard_b = build_cross_shard_b();

    // (1) Per-shard verification of shard B ALONE: CrossB cannot resolve CrossA,
    // so its axiom registration is rejected by the kernel (unknown constant).
    let prelude = Environment::try_with_prelude().expect("kernel prelude environment");
    let solo = verify_shard_incremental_with_env(&shard_b, prelude);
    assert_eq!(solo.total, 1);
    assert_eq!(
        solo.kernel_verified, 0,
        "shard B alone must NOT verify the cross-shard constant: {:?}",
        solo.failures
    );
    assert_eq!(
        solo.failed, 1,
        "CrossB should be rejected for an unresolved external dependency: {:?}",
        solo.failures
    );
    assert!(
        solo.failures.iter().any(|(name, _)| name == "CrossB"),
        "failure must be attributed to CrossB: {:?}",
        solo.failures
    );

    // (2) Load BOTH shards into one MathverseLibrary and run the corpus
    // verifier: the merged dependency graph now contains the A→B edge, so
    // CrossA is registered before CrossB in global topological order and CrossB
    // verifies.
    let mut library = MathverseLibrary::new(TrustPolicy::permissive());
    assert_eq!(library.load_shard(&shard_a).unwrap(), 1);
    assert_eq!(library.load_shard(&shard_b).unwrap(), 1);
    assert_eq!(library.constant_count(), 2);

    let prelude = Environment::try_with_prelude().expect("kernel prelude environment");
    let corpus = verify_corpus_incremental(&library, prelude);
    assert_eq!(corpus.total, 2, "corpus covers both merged constants");
    // CrossA and CrossB are NO_VALUE axioms: the kernel accepts them as
    // well-formed axioms but does NOT proof-check them, so they are
    // AxiomAccepted, not KernelVerified. The load-bearing point is that the
    // cross-shard dependency RESOLVES — CrossB's axiom registration is accepted
    // (no ReconstructFailed / KernelRejected) once CrossA is in scope.
    assert_eq!(
        corpus.axiom_accepted, 2,
        "the merged corpus must accept BOTH CrossA and the cross-shard CrossB as axioms: {:?}",
        corpus.failures
    );
    assert_eq!(
        corpus.kernel_verified, 0,
        "NO_VALUE axioms are not genuinely kernel-verified: {:?}",
        corpus.failures
    );
    assert_eq!(
        corpus.failed, 0,
        "no failures expected: {:?}",
        corpus.failures
    );
    assert_eq!(corpus.reconstruct_failed, 0);
    assert_eq!(corpus.cycle_skipped, 0);

    // The genuine verdict set length must match the count, and a NO_VALUE axiom
    // must NOT appear in it (the manifest must not overcount CrossB as a
    // proof-check).
    assert_eq!(
        corpus.kernel_verified_names.len(),
        corpus.kernel_verified,
        "verdict-name set length must match the kernel_verified count"
    );
    assert!(
        !corpus.kernel_verified_names.contains(&"CrossB".to_string()),
        "NO_VALUE axiom CrossB must NOT be in the genuine kernel-verified verdict set: {:?}",
        corpus.kernel_verified_names
    );
}

/// The consume side: applying a kernel-verified manifest upgrades the in-memory
/// `import_confidence` of named constants to `KernelVerified` (and skips names
/// absent from the library).
///
/// `Foo` is a value-bearing `Definition` with a genuinely well-typed value
/// (`Foo : Type 0 := Prop`, i.e. `Sort 0 : Sort 1`), so it is honestly
/// `KernelVerified` by the corpus verifier and lands in `kernel_verified_names`
/// and the derived manifest. A `NO_VALUE` axiom would instead be
/// `AxiomAccepted` and absent from the verdict set, which would not exercise the
/// upgrade.
#[test]
fn test_kernel_verified_manifest_upgrades_confidence() {
    use super::verify_corpus_incremental;
    use crate::library::MathverseLibrary;
    use crate::trust::policy::TrustPolicy;
    use crate::verify::kernel_verified_manifest::KernelVerifiedManifest;

    // A shard with one Translated definition `Foo : Type 0 := Prop`. The value
    // `Sort 0` (Prop) genuinely typechecks against the declared type `Sort 1`
    // (Type 0), so the kernel proof-checks it.
    let mut writer = ShardWriter::new();
    let name = writer.add_string("Foo");
    let l_zero = writer.add_level(FlatLevel::zero());
    let l_one = writer.add_level(FlatLevel::succ(l_zero));
    let ty = writer.add_expr(FlatExpr::sort(l_one)); // Foo : Type 0
    let value = writer.add_expr(FlatExpr::sort(l_zero)); // Foo := Prop
    writer.add_constant(MathverseConstantHeader {
        name_idx: name,
        type_idx: ty,
        value_idx: value,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::Translated as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Definition as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let shard = ShardReader::from_bytes(&buf).unwrap();

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();

    let kv = ImportConfidence::KernelVerified as u8;
    let foo_conf = |lib: &MathverseLibrary| {
        let idx = lib.lookup_constant_idx("Foo").unwrap();
        lib.get_constant(idx).unwrap().import_confidence
    };
    assert_ne!(foo_conf(&lib), kv, "Foo starts below KernelVerified");

    // Derive the manifest from a genuine corpus verification run: Foo's value
    // typechecks, so it is honestly KernelVerified and appears in the manifest.
    let prelude = Environment::try_with_prelude().expect("kernel prelude environment");
    let report = verify_corpus_incremental(&lib, prelude);
    assert_eq!(
        report.kernel_verified, 1,
        "value-bearing Foo must be genuinely kernel-verified: failures = {:?}",
        report.failures
    );
    assert_eq!(report.axiom_accepted, 0);
    assert_eq!(report.axiom_fallback, 0);

    let mut manifest = KernelVerifiedManifest::from_report("", 1, &report);
    assert!(manifest.kernel_verified_names.contains(&"Foo".to_string()));
    // An absent name must be skipped at apply time.
    manifest.kernel_verified_names.push("Absent".to_string());

    let upgraded = lib.apply_kernel_verified_manifest(&manifest);

    assert_eq!(upgraded, 1, "Foo upgraded; Absent (not in library) skipped");
    assert_eq!(
        foo_conf(&lib),
        kv,
        "Foo -> KernelVerified after applying the manifest"
    );
}

/// WS5 end-to-end: build a tiny shard with a genuinely kernel-checkable
/// definition written at a *below*-`KernelVerified` confidence, write it to
/// disk, re-verify the corpus in the Clean kernel, stamp the verdict into the
/// shard **bytes** on disk, reload from disk, and assert the stored
/// `KernelVerified` count is non-zero and matches the kernel's verdict.
///
/// This is the proof the WS5 edge is wired: today every shipped shard stores
/// `KernelVerified = 0` because nothing persists the kernel verdict. Here the
/// stamp survives a full disk round-trip.
///
/// SOUNDNESS: the stamped name comes ONLY from `verify_corpus_incremental`'s
/// `kernel_verified_names` — `Foo`'s value `Sort 0` genuinely typechecks against
/// its declared type `Sort 1` through `add_decl`'s `check_type`. No heuristic
/// confidence is ever promoted.
#[test]
fn test_ws5_stamp_kernel_verified_persists_through_disk_roundtrip() {
    use super::verify_corpus_incremental;
    use crate::library::{
        count_stored_kernel_verified, stamp_shard_dir_kernel_verified, MathverseLibrary,
    };
    use crate::trust::policy::TrustPolicy;
    use crate::verify::kernel_verified_manifest::KernelVerifiedManifest;

    // (1) Build a shard with `Foo : Type 0 := Prop`, written at `Translated`
    // confidence (NOT KernelVerified) so the stamp is an observable transition.
    let mut writer = ShardWriter::new();
    let name = writer.add_string("Foo");
    let l_zero = writer.add_level(FlatLevel::zero());
    let l_one = writer.add_level(FlatLevel::succ(l_zero));
    let ty = writer.add_expr(FlatExpr::sort(l_one)); // Foo : Type 0
    let value = writer.add_expr(FlatExpr::sort(l_zero)); // Foo := Prop
    writer.add_constant(MathverseConstantHeader {
        name_idx: name,
        type_idx: ty,
        value_idx: value,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::Translated as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Definition as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();

    let dir = tempfile::tempdir().expect("tempdir");
    let shard_path = dir.path().join("Foo.mathverse");
    std::fs::write(&shard_path, &buf).expect("write shard to disk");

    // Pre-condition: stored KernelVerified == 0 (the status quo this WS fixes).
    let (before, unreadable) =
        count_stored_kernel_verified(dir.path()).expect("count stored before");
    assert!(
        unreadable.is_empty(),
        "shard must be readable: {unreadable:?}"
    );
    assert_eq!(
        before, 0,
        "freshly built shard must store KernelVerified = 0"
    );

    // (2) Re-verify the corpus in the Clean kernel to obtain the GENUINE verdict.
    let shard = ShardReader::from_bytes(&buf).unwrap();
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    let prelude = Environment::try_with_prelude().expect("kernel prelude environment");
    let report = verify_corpus_incremental(&lib, prelude);
    assert_eq!(
        report.kernel_verified, 1,
        "value-bearing Foo must be genuinely kernel-verified: failures = {:?}",
        report.failures
    );
    assert!(report.kernel_verified_names.contains(&"Foo".to_string()));

    let manifest =
        KernelVerifiedManifest::from_report(&dir.path().display().to_string(), 1, &report);

    // (3) DESTRUCTIVE on-disk stamp: rewrite the shard bytes so Foo carries
    // KernelVerified in its persisted header.
    let stamp = stamp_shard_dir_kernel_verified(dir.path(), &manifest).expect("stamp on disk");
    assert_eq!(stamp.shards_rewritten, 1, "the single shard is rewritten");
    assert_eq!(stamp.constants_stamped, 1, "Foo's header byte is raised");

    // (4) Reload from DISK (not the in-memory writer) and assert the stamp
    // survived into the bytes.
    let (after, unreadable_after) =
        count_stored_kernel_verified(dir.path()).expect("count stored after");
    assert!(
        unreadable_after.is_empty(),
        "rewritten shard must remain a valid, checksummed shard: {unreadable_after:?}"
    );
    assert_eq!(
        after, 1,
        "stored KernelVerified must be > 0 after the on-disk stamp"
    );

    // The reloaded header genuinely reads KernelVerified, and the rest of the
    // shard round-trips unchanged (Foo's type/value indices still resolve).
    let reloaded = ShardReader::from_file(&shard_path).expect("reload stamped shard");
    let foo = reloaded
        .constants
        .iter()
        .find(|c| {
            reloaded
                .strings
                .get(c.name_idx as usize)
                .map(String::as_str)
                == Some("Foo")
        })
        .expect("Foo present after rewrite");
    assert_eq!(
        foo.import_confidence,
        ImportConfidence::KernelVerified as u8,
        "Foo reads KernelVerified from the stamped bytes"
    );

    // Idempotence: re-stamping the already-stamped dir raises nothing further.
    let restamp = stamp_shard_dir_kernel_verified(dir.path(), &manifest).expect("restamp");
    assert_eq!(
        restamp.constants_stamped, 0,
        "already-stamped header is not re-raised"
    );
    assert_eq!(restamp.shards_rewritten, 0);
}

/// WS5 release gate: after the shards are stamped from a kernel-verified
/// manifest, `verify_release`'s stored-`KernelVerified`-count assertion
/// (`assert_kernel_verified_stamp`) passes; reverting a shard to its un-stamped
/// bytes while the manifest still lists the name makes the gate fail. This
/// proves the assertion is load bearing.
///
/// Does NOT invoke `package_release_with_stamp` directly so the test stays
/// independent of the host `tar`/`zstd` binaries; it drives the same
/// stamp-then-assert sequence that packaging performs.
#[test]
fn test_ws5_release_verify_asserts_persisted_stamp_count() {
    use super::verify_corpus_incremental;
    use crate::library::{stamp_shard_dir_kernel_verified, MathverseLibrary};
    use crate::release::assert_kernel_verified_stamp;
    use crate::trust::policy::TrustPolicy;
    use crate::verify::kernel_verified_manifest::KernelVerifiedManifest;

    // Build `Foo : Type 0 := Prop` at Translated confidence, on disk.
    let mut writer = ShardWriter::new();
    let name = writer.add_string("Foo");
    let l_zero = writer.add_level(FlatLevel::zero());
    let l_one = writer.add_level(FlatLevel::succ(l_zero));
    let ty = writer.add_expr(FlatExpr::sort(l_one));
    let value = writer.add_expr(FlatExpr::sort(l_zero));
    writer.add_constant(MathverseConstantHeader {
        name_idx: name,
        type_idx: ty,
        value_idx: value,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::Translated as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Definition as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();

    let dir = tempfile::tempdir().expect("tempdir");
    let shard_dir = dir.path().join("base");
    std::fs::create_dir_all(&shard_dir).unwrap();
    std::fs::write(shard_dir.join("Foo.mathverse"), &buf).unwrap();

    // Genuine verdict + manifest written alongside the shards.
    let shard = ShardReader::from_bytes(&buf).unwrap();
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    let prelude = Environment::try_with_prelude().expect("kernel prelude environment");
    let report = verify_corpus_incremental(&lib, prelude);
    let manifest =
        KernelVerifiedManifest::from_report(&shard_dir.display().to_string(), 1, &report);
    let manifest_path = shard_dir.join("kernel-verified.json");
    manifest.write_to_file(&manifest_path).unwrap();

    // Before stamping, the gate must already FAIL: the manifest lists Foo but
    // the bytes store KernelVerified = 0.
    let pre = assert_kernel_verified_stamp(&shard_dir)
        .expect_err("un-stamped shard must fail the persisted-count assertion");
    assert!(matches!(
        pre,
        crate::error::MathverseError::KernelVerifiedStampMismatch { .. }
    ));

    // Stamp on disk (the same step packaging performs before hashing), then the
    // gate must PASS: stored count == manifest names present on disk.
    stamp_shard_dir_kernel_verified(&shard_dir, &manifest).expect("stamp on disk");
    assert_kernel_verified_stamp(&shard_dir).expect("persisted stamp count matches manifest");

    // Negative case: revert the shard to its original (un-stamped) bytes while
    // the kernel-verified.json still lists `Foo`. Now `stored` (0) disagrees
    // with `expected` (1 header present and named in the manifest), so the gate
    // must fail with a stamp-count mismatch — proving the assertion is load
    // bearing, not a no-op.
    std::fs::write(shard_dir.join("Foo.mathverse"), &buf).unwrap();
    let err = assert_kernel_verified_stamp(&shard_dir)
        .expect_err("un-stamped shard must fail the persisted-count assertion");
    assert!(
        matches!(
            err,
            crate::error::MathverseError::KernelVerifiedStampMismatch { .. }
        ),
        "expected a stamp-count mismatch, got: {err}"
    );
}

/// Build shard A: polymorphic axiom `PolyA.{u} : Sort u`.
fn build_poly_shard_a() -> ShardReader {
    let mut writer = ShardWriter::new();
    let u_str = writer.add_string("u");
    let name_a = writer.add_string("PolyA");
    let l_u = writer.add_level(FlatLevel::param(u_str));
    let type_a = writer.add_expr(FlatExpr::sort(l_u)); // PolyA : Sort u

    writer.add_constant(MathverseConstantHeader {
        name_idx: name_a,
        type_idx: type_a,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Axiom as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: u_str,
        level_params_count: 1,
        _pad2: [0u8; 26],
    });

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

/// Build shard B: monomorphic axiom `PolyB : PolyA.{0}`.
///
/// Its type is a `Const` reference to `PolyA` carrying an explicit universe
/// argument list `[Level::zero]`, so it exercises the level_lists table — the
/// table this change starts merging + index-remapping into the library.
fn build_poly_shard_b() -> ShardReader {
    let mut writer = ShardWriter::new();
    let name_b = writer.add_string("PolyB");
    let name_a = writer.add_string("PolyA");

    // Universe argument list [Level::zero] for the PolyA reference.
    let l_zero = writer.add_level(FlatLevel::zero());
    let ll_offset = writer.add_level_list(&[l_zero]);
    let type_b = writer.add_expr(FlatExpr::const_ref(name_a, ll_offset)); // PolyB : PolyA.{0}

    writer.add_constant(MathverseConstantHeader {
        name_idx: name_b,
        type_idx: type_b,
        value_idx: NO_VALUE,
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

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

/// Cross-shard universe-polymorphic dependency: shard B's constant references a
/// polymorphic constant from shard A *with an explicit universe argument list*.
///
/// This is the level_lists-specific proof. The merge must offset shard B's
/// `Const.levels_list_idx` by B's level-lists base AND offset the level-pool
/// index stored inside that list (`Level::zero`) by B's level base; getting
/// either wrong would reconstruct the wrong universe argument and the corpus
/// verification would fail.
#[test]
fn test_cross_shard_universe_polymorphic_level_lists_merge() {
    use super::verify_corpus_incremental;
    use crate::library::MathverseLibrary;
    use crate::trust::policy::TrustPolicy;

    let shard_a = build_poly_shard_a();
    let shard_b = build_poly_shard_b();

    // Per-shard B alone cannot resolve PolyA → its axiom registration fails.
    let prelude = Environment::try_with_prelude().expect("kernel prelude environment");
    let solo = verify_shard_incremental_with_env(&shard_b, prelude);
    assert_eq!(
        solo.kernel_verified, 0,
        "B alone must fail: {:?}",
        solo.failures
    );

    // Load A then B; the level_lists table is merged with B's records appended
    // after A's (A contributes none here, but B's level pool/level-lists bases
    // are still shifted by A's arena sizes).
    let mut library = MathverseLibrary::new(TrustPolicy::permissive());
    library.load_shard(&shard_a).unwrap();
    library.load_shard(&shard_b).unwrap();

    // The merged level_lists must contain B's record `[count=1, <remapped zero idx>]`.
    assert!(
        !library.level_lists().is_empty(),
        "merged library must carry the level_lists record from shard B"
    );

    let prelude = Environment::try_with_prelude().expect("kernel prelude environment");
    let corpus = verify_corpus_incremental(&library, prelude);
    assert_eq!(corpus.total, 2);
    // PolyA and PolyB are NO_VALUE axioms → AxiomAccepted. The proof here is that
    // the polymorphic cross-shard reference (PolyA.{0}) RESOLVES and its axiom
    // registration is accepted under the corpus loader (no failures), not that it
    // is proof-checked.
    assert_eq!(
        corpus.axiom_accepted, 2,
        "polymorphic cross-shard reference (PolyA.{{0}}) must resolve and be axiom-accepted under the corpus loader: {:?}",
        corpus.failures
    );
    assert_eq!(corpus.kernel_verified, 0);
    assert_eq!(
        corpus.failed, 0,
        "no failures expected: {:?}",
        corpus.failures
    );
    assert_eq!(corpus.reconstruct_failed, 0);
}

/// Build the masked-failure taint fixture:
/// - `P : Prop`                  (axiom carrier)
/// - `B : P := (λ x:P, x)`       (value has type `P → P` ≠ `P`: the kernel
///                                REJECTS the value; `try_add_decl` registers `B`
///                                as an axiom of type `P` — a masked failure,
///                                `AxiomFallback(Some)`)
/// - `T : P := B`                (typechecks ONLY against `B`-as-axiom →
///                                `add_decl` returns `KernelVerified`)
/// - `idP : P → P := (λ x:P, x)` (genuinely valid — positive control that the
///                                fix does NOT over-withhold)
fn build_masked_failure_taint_shard() -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let p_name = writer.add_string("P");
    let b_name = writer.add_string("B");
    let t_name = writer.add_string("T");
    let id_name = writer.add_string("idP");

    let p_const = writer.add_expr(FlatExpr::const_ref(p_name, u32::MAX));
    let p_to_p = writer.add_expr(FlatExpr::pi(0, p_const, p_const));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    // λ (x : P), x  — has type `P → P`.
    let lam_p = writer.add_expr(FlatExpr::lam(0, p_const, bvar0));
    let b_const = writer.add_expr(FlatExpr::const_ref(b_name, u32::MAX));

    let mk = |name_idx, type_idx, value_idx, decl_kind: DeclKind| MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: decl_kind as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };

    // P : Prop
    writer.add_constant(mk(p_name, sort_prop, NO_VALUE, DeclKind::Axiom));
    // B : P := (λ x:P, x)  — value type `P → P` ≠ declared `P` → masked failure.
    writer.add_constant(mk(b_name, p_const, lam_p, DeclKind::Theorem));
    // T : P := B  — typechecks against B-as-axiom.
    writer.add_constant(mk(t_name, p_const, b_const, DeclKind::Theorem));
    // idP : P → P := (λ x:P, x)  — genuinely valid, independent of B.
    writer.add_constant(mk(id_name, p_to_p, lam_p, DeclKind::Definition));

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

#[test]
fn test_masked_failure_taint_not_laundered_to_kernel_verified() {
    // SOUNDNESS (masked-failure taint): a value-bearing decl `B` whose value the
    // kernel REJECTS is registered as an axiom so dependents still resolve. A
    // dependent `T := B` then typechecks against that fabricated axiom and
    // `add_decl` returns `KernelVerified`. Before the fix, `T` landed in
    // `kernel_verified_names` and was stamped `ImportConfidence::KernelVerified`
    // on the shard — laundering a proof the kernel actively refused. The fix
    // propagates the taint through the dependency graph and WITHHOLDS the verdict
    // from `T` (and every transitive dependent), while leaving genuinely-verified
    // constants alone.
    let reader = build_masked_failure_taint_shard();
    let report = verify_shard_incremental(&reader);

    // B is a masked failure: its rejected value is recorded, and it is NOT
    // itself kernel-verified.
    assert!(
        report
            .axiom_fallback_names
            .iter()
            .any(|(name, _)| name == "B"),
        "B's rejected value must be recorded as a masked-failure axiom fallback: {:?}",
        report.axiom_fallback_names
    );
    assert!(
        !report.kernel_verified_names.iter().any(|n| n == "B"),
        "B (an axiom fallback) must never be kernel-verified"
    );

    // THE FIX: T rests transitively on the fabricated axiom B, so it must be
    // withheld from the KernelVerified verdict — never stamped as such.
    assert!(
        !report.kernel_verified_names.iter().any(|n| n == "T"),
        "T rests on a masked-failure axiom and must NOT be kernel-verified \
         (else it would be stamped ImportConfidence::KernelVerified): {:?}",
        report.kernel_verified_names
    );
    assert!(
        report
            .failures
            .iter()
            .any(|(name, msg)| name == "T" && msg.contains("trust-withheld")),
        "T must be surfaced as trust-withheld for audit: {:?}",
        report.failures
    );

    // POSITIVE CONTROL: a genuinely-verified constant independent of B is not
    // over-withheld.
    assert!(
        report.kernel_verified_names.iter().any(|n| n == "idP"),
        "the genuinely-valid idP must remain kernel-verified (no over-withholding): {:?}",
        report.kernel_verified_names
    );
}

// ---------------------------------------------------------------------------
// STAND-IN-BLOCKED rejection classification (the −164 record-chain lever):
// a value rejection whose dependency set includes a VALUE-LESS STAND-IN
// (dump-salvaged `SALVAGED_STAND_IN` axiom / family stand-in) is a
// reconstruction gap, not a refused proof — clean type-only fallback, NO
// masked-failure taint. Both directions are pinned: with the stand-in
// evidence the dependent chain stays KernelVerified; without it (or when the
// rejection ALSO rests on genuine taint) the taint semantics are byte-
// identical to the pre-lever baseline.
// ---------------------------------------------------------------------------

/// Build the stand-in-blocked classification fixture (the mathcomp
/// `Ring.sort`-chain shape in miniature):
/// - `P : Prop` — value-less axiom carrier; `p_profile` controls whether it
///   carries the dump-salvage `SALVAGED_STAND_IN` provenance hint.
/// - `B : P := (λ x:P, x)` — value has type `P → P` ≠ `P`: the kernel REJECTS
///   the value (its dependency set is exactly `{P}`), and `try_add_decl`
///   registers `B` as an axiom of its stated type.
/// - `T : P := B` — typechecks against `B`-as-axiom.
fn build_standin_blocked_shard(p_profile: AxiomProfile) -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let p_name = writer.add_string("P");
    let b_name = writer.add_string("B");
    let t_name = writer.add_string("T");

    let p_const = writer.add_expr(FlatExpr::const_ref(p_name, u32::MAX));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    // λ (x : P), x — has type `P → P`, so it is rejected at declared type `P`.
    let lam_p = writer.add_expr(FlatExpr::lam(0, p_const, bvar0));
    let b_const = writer.add_expr(FlatExpr::const_ref(b_name, u32::MAX));

    let mk =
        |name_idx, type_idx, value_idx, decl_kind: DeclKind, profile| MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::Axiomatized as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind as u8,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

    writer.add_constant(mk(p_name, sort_prop, NO_VALUE, DeclKind::Axiom, p_profile));
    writer.add_constant(mk(
        b_name,
        p_const,
        lam_p,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));
    writer.add_constant(mk(
        t_name,
        p_const,
        b_const,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

#[test]
fn test_standin_blocked_rejection_classified_clean_dependent_stays_kernel_verified() {
    // DIRECTION 1 (the lever): `P` carries the dump-salvage stand-in hint, so
    // `B`'s value rejection (deps = {P}) is a reconstruction gap — classified
    // on the stand-in-blocked lane, NO taint seeded, and the dependent `T`
    // (whose value genuinely typechecks against `B`'s kernel-checked stated
    // type) keeps its KernelVerified verdict.
    let reader =
        build_standin_blocked_shard(AxiomProfile::AXIOMATIZED | AxiomProfile::SALVAGED_STAND_IN);
    let report = verify_shard_incremental(&reader);

    assert!(
        report
            .standin_blocked_fallbacks
            .iter()
            .any(|(name, _)| name == "B"),
        "B's rejection is blocked by the value-less stand-in P and must land on \
         the stand-in-blocked lane: {:?}",
        report.standin_blocked_fallbacks
    );
    assert!(
        !report.axiom_fallback_names.iter().any(|(n, _)| n == "B"),
        "a stand-in-blocked rejection must NOT be recorded as a masked failure: {:?}",
        report.axiom_fallback_names
    );
    assert!(
        !report.kernel_verified_names.iter().any(|n| n == "B"),
        "B itself is a type-only fallback and must never be kernel-verified"
    );
    assert!(
        report.kernel_verified_names.iter().any(|n| n == "T"),
        "T's value typechecks and B seeded no taint, so T must stay \
         kernel-verified (the lever's payoff): failures={:?}",
        report.failures
    );
    assert_eq!(
        report.failed, 0,
        "no trust-withheld failures expected: {:?}",
        report.failures
    );
}

#[test]
fn test_value_rejection_without_standin_evidence_still_seeds_taint() {
    // DIRECTION 2 (the guard): identical shard, but `P` is an ORDINARY axiom
    // (no stand-in hint). The classification must not fire — `B` seeds
    // masked-failure taint and `T` is trust-withheld, byte-identical to the
    // pre-lever baseline.
    let reader = build_standin_blocked_shard(AxiomProfile::AXIOMATIZED);
    let report = verify_shard_incremental(&reader);

    assert!(
        report.standin_blocked_fallbacks.is_empty(),
        "no stand-in evidence → nothing may be classified stand-in-blocked: {:?}",
        report.standin_blocked_fallbacks
    );
    assert!(
        report.axiom_fallback_names.iter().any(|(n, _)| n == "B"),
        "B's rejected value must stay a masked-failure fallback: {:?}",
        report.axiom_fallback_names
    );
    assert!(
        !report.kernel_verified_names.iter().any(|n| n == "T"),
        "T rests on the masked failure B and must be withheld: {:?}",
        report.kernel_verified_names
    );
    assert!(
        report
            .failures
            .iter()
            .any(|(name, msg)| name == "T" && msg.contains("trust-withheld")),
        "T must be surfaced as trust-withheld: {:?}",
        report.failures
    );
}

#[test]
fn test_standin_blocked_classification_never_overrides_genuine_taint() {
    // PRECEDENCE GUARD: a rejection whose dependencies include BOTH a marked
    // stand-in AND a genuine masked-failure taint keeps FULL taint semantics —
    // the stand-in evidence can never launder a taint chain.
    //
    // Fixture:
    // - `Q : Prop` ordinary axiom; `P : Prop` marked stand-in.
    // - `B1 : Q := (λ x:Q, x)` — rejected, deps {Q} (no stand-in) → taints.
    // - `C  : Q := (λ x:P, B1)` — rejected (type `P → Q` ≠ `Q`), deps
    //   {P, Q, B1}: stand-in involved AND rests on taint → must taint.
    // - `D  : Q := C` — typechecks against C-as-axiom → must be withheld.
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let q_name = writer.add_string("Q");
    let p_name = writer.add_string("P");
    let b1_name = writer.add_string("B1");
    let c_name = writer.add_string("C");
    let d_name = writer.add_string("D");

    let q_const = writer.add_expr(FlatExpr::const_ref(q_name, u32::MAX));
    let p_const = writer.add_expr(FlatExpr::const_ref(p_name, u32::MAX));
    let b1_const = writer.add_expr(FlatExpr::const_ref(b1_name, u32::MAX));
    let c_const = writer.add_expr(FlatExpr::const_ref(c_name, u32::MAX));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    let lam_q = writer.add_expr(FlatExpr::lam(0, q_const, bvar0)); // λ x:Q, x : Q → Q
    let lam_p_b1 = writer.add_expr(FlatExpr::lam(0, p_const, b1_const)); // λ x:P, B1 : P → Q

    let mk =
        |name_idx, type_idx, value_idx, decl_kind: DeclKind, profile| MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::Axiomatized as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind as u8,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

    writer.add_constant(mk(
        q_name,
        sort_prop,
        NO_VALUE,
        DeclKind::Axiom,
        AxiomProfile::AXIOMATIZED,
    ));
    writer.add_constant(mk(
        p_name,
        sort_prop,
        NO_VALUE,
        DeclKind::Axiom,
        AxiomProfile::AXIOMATIZED | AxiomProfile::SALVAGED_STAND_IN,
    ));
    writer.add_constant(mk(
        b1_name,
        q_const,
        lam_q,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));
    writer.add_constant(mk(
        c_name,
        q_const,
        lam_p_b1,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));
    writer.add_constant(mk(
        d_name,
        q_const,
        c_const,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();
    let report = verify_shard_incremental(&reader);

    assert!(
        report.axiom_fallback_names.iter().any(|(n, _)| n == "B1"),
        "B1 (no stand-in dep) must stay a masked failure: {:?}",
        report.axiom_fallback_names
    );
    assert!(
        report.axiom_fallback_names.iter().any(|(n, _)| n == "C"),
        "C rests on the tainted B1 — genuine taint takes precedence over its \
         stand-in dep, so C must stay a masked failure: fallbacks={:?} \
         standin_blocked={:?}",
        report.axiom_fallback_names,
        report.standin_blocked_fallbacks
    );
    assert!(
        !report
            .standin_blocked_fallbacks
            .iter()
            .any(|(n, _)| n == "C"),
        "C must NOT be laundered onto the stand-in-blocked lane: {:?}",
        report.standin_blocked_fallbacks
    );
    assert!(
        !report.kernel_verified_names.iter().any(|n| n == "D"),
        "D rests transitively on the masked failures and must be withheld: {:?}",
        report.kernel_verified_names
    );
}

#[test]
fn test_standin_blocked_fallback_extends_the_standin_wall() {
    // CHAIN PROPAGATION: a stand-in-blocked fallback is itself a value-less
    // registration of a source-checked value, so a SECOND-order rejection
    // blocked at it (deps = {F} only, never touching the root stand-in S) is
    // still classified clean — the mathcomp chains are multi-level.
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let s_name = writer.add_string("S");
    let f_name = writer.add_string("F");
    let g_name = writer.add_string("G");

    let s_const = writer.add_expr(FlatExpr::const_ref(s_name, u32::MAX));
    let f_const = writer.add_expr(FlatExpr::const_ref(f_name, u32::MAX));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    // λ x:S, x : S → S — rejected at declared type Prop; deps {S}.
    let lam_s = writer.add_expr(FlatExpr::lam(0, s_const, bvar0));
    // λ x:F, x : F → F — rejected at declared type Prop; deps {F} ONLY.
    let lam_f = writer.add_expr(FlatExpr::lam(0, f_const, bvar0));

    let mk =
        |name_idx, type_idx, value_idx, decl_kind: DeclKind, profile| MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::Axiomatized as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind as u8,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

    writer.add_constant(mk(
        s_name,
        sort_prop,
        NO_VALUE,
        DeclKind::Axiom,
        AxiomProfile::AXIOMATIZED | AxiomProfile::SALVAGED_STAND_IN,
    ));
    writer.add_constant(mk(
        f_name,
        sort_prop,
        lam_s,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));
    writer.add_constant(mk(
        g_name,
        sort_prop,
        lam_f,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();
    let report = verify_shard_incremental(&reader);

    for name in ["F", "G"] {
        assert!(
            report
                .standin_blocked_fallbacks
                .iter()
                .any(|(n, _)| n == name),
            "{name} must be classified stand-in-blocked (F via the marked S, \
             G via the stand-in wall F extends): {:?}",
            report.standin_blocked_fallbacks
        );
    }
    assert!(
        report.axiom_fallback_names.is_empty(),
        "no masked failures expected in the pure stand-in chain: {:?}",
        report.axiom_fallback_names
    );
    assert_eq!(
        report.failed, 0,
        "no trust-withheld failures expected: {:?}",
        report.failures
    );
}

// ---------------------------------------------------------------------------
// TRANSITIVE stand-in-blocked classification (the masked-seed chain-root
// lever, 2026-07-12): the kernel's conversion δ-unfolds the VALUES of
// intermediate — even kernel-verified — constants, so a value rejection can
// hit the opaque stand-in wall with NO direct stand-in dependency. Measured
// at the 20,234-KV baseline: the dominant taint-chain roots (mathcomp
// poly_ringType / subsetP / int_ZmodType, stdlib Zquot / Qminmax) are exactly
// this shape. Both directions pinned, plus taint precedence.
// ---------------------------------------------------------------------------

/// Build the transitive-wall fixture:
/// - `P : Prop` — value-less carrier; `p_profile` controls the stand-in hint.
/// - `M : Prop := P` — value typechecks (KernelVerified); deps `{P}`. The
///   kernel CAN δ-unfold `M`, so `M` carries the wall in its unfolded value.
/// - `B : M := (λ x:M, x)` — value has type `M → M` ≠ `M`: rejected. Direct
///   deps are `{M}` ONLY — no direct stand-in — the wall is one hop deep.
/// - `T : M := B` — typechecks against `B`'s kernel-checked stated type.
fn build_transitive_standin_shard(p_profile: AxiomProfile) -> ShardReader {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let p_name = writer.add_string("P");
    let m_name = writer.add_string("M");
    let b_name = writer.add_string("B");
    let t_name = writer.add_string("T");

    let p_const = writer.add_expr(FlatExpr::const_ref(p_name, u32::MAX));
    let m_const = writer.add_expr(FlatExpr::const_ref(m_name, u32::MAX));
    let b_const = writer.add_expr(FlatExpr::const_ref(b_name, u32::MAX));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    // λ (x : M), x — has type `M → M`, rejected at declared type `M`.
    let lam_m = writer.add_expr(FlatExpr::lam(0, m_const, bvar0));

    let mk =
        |name_idx, type_idx, value_idx, decl_kind: DeclKind, profile| MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::Axiomatized as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind as u8,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

    writer.add_constant(mk(p_name, sort_prop, NO_VALUE, DeclKind::Axiom, p_profile));
    writer.add_constant(mk(
        m_name,
        sort_prop,
        p_const,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));
    writer.add_constant(mk(
        b_name,
        m_const,
        lam_m,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));
    writer.add_constant(mk(
        t_name,
        m_const,
        b_const,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

#[test]
fn test_transitive_standin_blocked_rejection_classified_dependent_stays_kernel_verified() {
    // DIRECTION 1 (the lever): the wall `P` sits ONE HOP behind the
    // kernel-verified intermediate `M`. `B`'s rejection (direct deps `{M}`,
    // no direct stand-in) must classify on the stand-in-blocked lane via the
    // transitive reach, seed NO taint, and leave the dependent `T`
    // kernel-verified.
    let reader =
        build_transitive_standin_shard(AxiomProfile::AXIOMATIZED | AxiomProfile::SALVAGED_STAND_IN);
    let report = verify_shard_incremental(&reader);

    assert!(
        report.kernel_verified_names.iter().any(|n| n == "M"),
        "M's value genuinely typechecks and must stay kernel-verified: {:?}",
        report.kernel_verified_names
    );
    assert!(
        report
            .standin_blocked_fallbacks
            .iter()
            .any(|(name, _)| name == "B"),
        "B's rejection is blocked by the stand-in P one hop deep (through M) \
         and must land on the stand-in-blocked lane: {:?}",
        report.standin_blocked_fallbacks
    );
    assert!(
        !report.axiom_fallback_names.iter().any(|(n, _)| n == "B"),
        "a transitively stand-in-blocked rejection must NOT be recorded as a \
         masked failure: {:?}",
        report.axiom_fallback_names
    );
    assert!(
        report.kernel_verified_names.iter().any(|n| n == "T"),
        "T's value typechecks and B seeded no taint, so T must stay \
         kernel-verified: failures={:?}",
        report.failures
    );
    assert_eq!(
        report.failed, 0,
        "no trust-withheld failures expected: {:?}",
        report.failures
    );
}

#[test]
fn test_transitive_reach_without_standin_hint_still_seeds_taint() {
    // DIRECTION 2 (the guard): identical shard, but `P` is an ORDINARY axiom
    // (no stand-in hint) — nothing is reachable because nothing is a stand-in.
    // `B` must seed masked-failure taint and `T` must be withheld,
    // byte-identical to the baseline.
    let reader = build_transitive_standin_shard(AxiomProfile::AXIOMATIZED);
    let report = verify_shard_incremental(&reader);

    assert!(
        report.standin_blocked_fallbacks.is_empty(),
        "no stand-in evidence anywhere in the cone → nothing may be \
         classified stand-in-blocked: {:?}",
        report.standin_blocked_fallbacks
    );
    assert!(
        report.axiom_fallback_names.iter().any(|(n, _)| n == "B"),
        "B's rejected value must stay a masked-failure fallback: {:?}",
        report.axiom_fallback_names
    );
    assert!(
        !report.kernel_verified_names.iter().any(|n| n == "T"),
        "T rests on the masked failure B and must be withheld: {:?}",
        report.kernel_verified_names
    );
    assert!(
        report
            .failures
            .iter()
            .any(|(name, msg)| name == "T" && msg.contains("trust-withheld")),
        "T must be surfaced as trust-withheld: {:?}",
        report.failures
    );
}

#[test]
fn test_transitive_standin_reach_never_overrides_genuine_taint() {
    // PRECEDENCE GUARD: a rejection with a DIRECT masked-failure taint dep
    // keeps full taint semantics even when its cone ALSO reaches a stand-in
    // transitively — the reach can never launder a taint chain.
    //
    // Fixture:
    // - `P : Prop` marked stand-in; `M : Prop := P` (kernel-verified, carries
    //   the wall one hop deep); `Q : Prop` ordinary axiom.
    // - `B1 : Q := (λ x:Q, x)` — rejected, deps `{Q}` (no stand-in anywhere)
    //   → seeds taint.
    // - `C : Q := (λ x:M, B1)` — rejected (`M → Q` ≠ `Q`), deps `{M, Q, B1}`:
    //   stand-in reachable through M AND direct taint B1 → must stay tainted.
    // - `D : Q := C` — typechecks against C-as-axiom → must be withheld.
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let p_name = writer.add_string("P");
    let m_name = writer.add_string("M");
    let q_name = writer.add_string("Q");
    let b1_name = writer.add_string("B1");
    let c_name = writer.add_string("C");
    let d_name = writer.add_string("D");

    let p_const = writer.add_expr(FlatExpr::const_ref(p_name, u32::MAX));
    let m_const = writer.add_expr(FlatExpr::const_ref(m_name, u32::MAX));
    let q_const = writer.add_expr(FlatExpr::const_ref(q_name, u32::MAX));
    let b1_const = writer.add_expr(FlatExpr::const_ref(b1_name, u32::MAX));
    let c_const = writer.add_expr(FlatExpr::const_ref(c_name, u32::MAX));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    let lam_q = writer.add_expr(FlatExpr::lam(0, q_const, bvar0)); // Q → Q
    let lam_m_b1 = writer.add_expr(FlatExpr::lam(0, m_const, b1_const)); // M → Q

    let mk =
        |name_idx, type_idx, value_idx, decl_kind: DeclKind, profile| MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::Axiomatized as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind as u8,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

    writer.add_constant(mk(
        p_name,
        sort_prop,
        NO_VALUE,
        DeclKind::Axiom,
        AxiomProfile::AXIOMATIZED | AxiomProfile::SALVAGED_STAND_IN,
    ));
    writer.add_constant(mk(
        m_name,
        sort_prop,
        p_const,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));
    writer.add_constant(mk(
        q_name,
        sort_prop,
        NO_VALUE,
        DeclKind::Axiom,
        AxiomProfile::AXIOMATIZED,
    ));
    writer.add_constant(mk(
        b1_name,
        q_const,
        lam_q,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));
    writer.add_constant(mk(
        c_name,
        q_const,
        lam_m_b1,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));
    writer.add_constant(mk(
        d_name,
        q_const,
        c_const,
        DeclKind::Definition,
        AxiomProfile::NONE,
    ));

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();
    let report = verify_shard_incremental(&reader);

    assert!(
        report.axiom_fallback_names.iter().any(|(n, _)| n == "B1"),
        "B1 (no stand-in anywhere in its cone) must stay a masked failure: {:?}",
        report.axiom_fallback_names
    );
    assert!(
        report.axiom_fallback_names.iter().any(|(n, _)| n == "C"),
        "C rests on the tainted B1 — genuine taint takes precedence over the \
         transitive stand-in reach through M: fallbacks={:?} standin_blocked={:?}",
        report.axiom_fallback_names,
        report.standin_blocked_fallbacks
    );
    assert!(
        !report
            .standin_blocked_fallbacks
            .iter()
            .any(|(n, _)| n == "C"),
        "C must NOT be laundered onto the stand-in-blocked lane by the \
         transitive reach: {:?}",
        report.standin_blocked_fallbacks
    );
    assert!(
        !report.kernel_verified_names.iter().any(|n| n == "D"),
        "D rests transitively on the masked failures and must be withheld: {:?}",
        report.kernel_verified_names
    );
}

// ---------------------------------------------------------------------------
// WS14: kernel-synthesized inductive-family member dedup
//
// After a family root replays through checked `add_inductive`, the shard ships
// its own copies of every generated member — the constructor, the recursor-table
// entries (`.rec`/`.casesOn`/`.recOn`), and the reducible `.noConfusion(Type)`
// defs. These must be RECOGNIZED as the already-checked member (KernelVerified),
// never re-added (which collides as `Duplicate declaration`) and never rejected
// merely because Lean's binder annotations differ from Clean's. A copy whose
// type genuinely differs — or a name that is NOT a synthesized member — must
// still fail closed.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod ws14_family_member_dedup_tests {
    use super::super::{try_accept_existing_inductive_family_constant, AddConstResult};
    use crate::inductive_replay::ReconstructedConstant;
    use crate::types::DeclKind;
    use clean_kernel::expr::{BinderData, BinderInfo, Expr};
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
    use clean_kernel::{Environment, Multiplicity, Name};

    /// A prelude env carrying a checked non-Prop inductive `WS14Foo : Type` with
    /// constructors `WS14Foo.a` and `WS14Foo.b`. `add_inductive` synthesizes the
    /// recursor table (`.rec`/`.casesOn`/`.recOn`) and the reducible
    /// `.noConfusion(Type)` defs for it.
    fn env_with_ws14foo() -> Environment {
        let mut env = Environment::try_with_prelude().expect("prelude");
        let foo = Name::from_string("WS14Foo");
        let foo_ref = Expr::const_(foo.clone(), vec![]);
        let decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: foo.clone(),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: Name::from_string("WS14Foo.a"),
                        type_: foo_ref.clone(),
                    },
                    Constructor {
                        name: Name::from_string("WS14Foo.b"),
                        type_: foo_ref,
                    },
                ],
            }],
        };
        env.add_inductive(decl).expect("WS14Foo add_inductive");
        env
    }

    /// Build a `ReconstructedConstant` mirroring a shard-resident member copy.
    fn recon(name: &str, kind: DeclKind, type_expr: Expr) -> ReconstructedConstant {
        ReconstructedConstant {
            decl_name: Name::from_string(name),
            decl_kind: kind,
            level_params: Vec::new(),
            type_expr,
            value_expr: None,
        }
    }

    /// Build a member copy that mirrors the env's existing member EXACTLY for
    /// level params, with the given (possibly rewritten) type. This is the
    /// realistic shard scenario: the shard's member carries the same universe
    /// params the kernel synthesized.
    fn recon_member(
        env: &Environment,
        name: &str,
        kind: DeclKind,
        type_expr: Expr,
    ) -> ReconstructedConstant {
        let level_params = env
            .get_const(&Name::from_string(name))
            .expect("member present in env")
            .level_params
            .clone();
        ReconstructedConstant {
            decl_name: Name::from_string(name),
            decl_kind: kind,
            level_params,
            type_expr,
            value_expr: None,
        }
    }

    /// Rewrite every `Pi` binder annotation to `Implicit` — the kernel's
    /// `is_def_eq` ignores binder info, so this is the SAME kernel type.
    fn flip_binder_info(expr: &Expr) -> Expr {
        use clean_kernel::expr::{ExprFolder, ExprKind};
        struct Flip;
        impl ExprFolder for Flip {
            fn fold_pi(&mut self, bd: BinderData, ty: &Expr, body: &Expr) -> Expr {
                let bd = BinderData::new(BinderInfo::Implicit, bd.mult);
                Expr::pi(bd, self.fold_expr(ty), self.fold_binder_body(body))
            }
        }
        // Only Pi-shaped recursor/casesOn types are interesting; for a leaf the
        // fold is a no-op clone.
        match expr.kind() {
            ExprKind::Pi(_, _, _) => Flip.fold_expr(expr),
            _ => expr.clone(),
        }
    }

    #[test]
    fn test_ws14_recursor_member_with_exact_type_accepted() {
        let env = env_with_ws14foo();
        let rec_ty = env
            .get_const(&Name::from_string("WS14Foo.rec"))
            .expect("synthesized WS14Foo.rec")
            .type_
            .clone();
        // Shard ships `.rec` as a Recursor-kind member with the exact type.
        let copy = recon_member(&env, "WS14Foo.rec", DeclKind::Recursor, rec_ty);
        let result = try_accept_existing_inductive_family_constant(&env, &copy);
        assert!(
            matches!(result, Some(AddConstResult::KernelVerified)),
            "exact-type synthesized recursor copy must be accepted, got {result:?}"
        );
    }

    #[test]
    fn test_ws14_caseson_definition_member_accepted_up_to_binder_info() {
        let env = env_with_ws14foo();
        // Lean ships `.casesOn` as a `Definition`; Clean installs it in the
        // recursor table. With Lean's binder annotations flipped, the copy must
        // STILL be accepted (binder-info-only difference is the same kernel type).
        let cases_ty = env
            .get_const(&Name::from_string("WS14Foo.casesOn"))
            .expect("synthesized WS14Foo.casesOn")
            .type_
            .clone();
        let flipped = flip_binder_info(&cases_ty);
        assert_ne!(flipped, cases_ty, "fixture must actually flip a binder");
        let copy = recon_member(&env, "WS14Foo.casesOn", DeclKind::Definition, flipped);
        let result = try_accept_existing_inductive_family_constant(&env, &copy);
        assert!(
            matches!(result, Some(AddConstResult::KernelVerified)),
            "Definition-kind casesOn copy differing only in binder info must be accepted, got {result:?}"
        );
    }

    #[test]
    fn test_ws14_no_confusion_definition_member_accepted() {
        let env = env_with_ws14foo();
        let nc_ty = env
            .get_const(&Name::from_string("WS14Foo.noConfusion"))
            .expect("synthesized WS14Foo.noConfusion (non-Prop family)")
            .type_
            .clone();
        let copy = recon_member(&env, "WS14Foo.noConfusion", DeclKind::Definition, nc_ty);
        let result = try_accept_existing_inductive_family_constant(&env, &copy);
        assert!(
            matches!(result, Some(AddConstResult::KernelVerified)),
            "synthesized noConfusion reducible-def copy must be accepted, got {result:?}"
        );
    }

    // ── Adversarial: a member copy with a genuinely wrong type must be REJECTED ──

    #[test]
    fn test_ws14_recon_member_wrong_type_rejected() {
        let env = env_with_ws14foo();
        // Same name as the synthesized recursor, but a bogus type (`Type → Type`
        // is not the recursor's type). Erasing binder info must NOT launder this.
        let bogus = Expr::pi(
            BinderData::new(BinderInfo::Default, Multiplicity::Many),
            Expr::type_(),
            Expr::type_(),
        );
        // Mirror the env member's level params so the rejection is forced by the
        // TYPE difference, not a level-params mismatch.
        let copy = recon_member(&env, "WS14Foo.recOn", DeclKind::Definition, bogus);
        let result = try_accept_existing_inductive_family_constant(&env, &copy);
        assert!(
            matches!(result, Some(AddConstResult::KernelRejected(ref m)) if m.contains("different type")),
            "a synthesized-member name carrying a genuinely different type must fail closed, got {result:?}"
        );
    }

    #[test]
    fn test_ws14_non_family_definition_falls_through() {
        let env = env_with_ws14foo();
        // `WS14Foo.helper` is NOT a kernel-synthesized member: it does not exist
        // in the env and its parent (WS14Foo) being an inductive does not make an
        // arbitrary child a synthesized member. The dispatch must return `None`
        // so the normal `add_decl` value-checking path handles it.
        let result = try_accept_existing_inductive_family_constant(
            &env,
            &recon("WS14Foo.helper", DeclKind::Definition, Expr::type_()),
        );
        assert!(
            result.is_none(),
            "a non-synthesized child Definition must fall through to normal replay, got {result:?}"
        );
    }

    #[test]
    fn test_ws14_no_confusion_with_non_inductive_parent_falls_through() {
        // `Foo.noConfusion` whose parent `Foo` is NOT a registered inductive
        // must NOT be treated as a synthesized member — it falls through so its
        // own value is proof-checked (and a genuine clash fails there).
        let env = Environment::try_with_prelude().expect("prelude");
        let result = try_accept_existing_inductive_family_constant(
            &env,
            &recon(
                "NotAnInductive.noConfusion",
                DeclKind::Definition,
                Expr::type_(),
            ),
        );
        assert!(
            result.is_none(),
            "noConfusion with a non-inductive parent must fall through, got {result:?}"
        );
    }

    /// A universe-polymorphic checked family for level-param alpha tests:
    /// `WS14PolyUnit.{u} : Sort (u+1)` with `mk : WS14PolyUnit`.
    fn env_with_ws14poly() -> Environment {
        let mut env = Environment::try_with_prelude().expect("prelude");
        let name = Name::from_string("WS14PolyUnit");
        let u = Name::from_string("u");
        let decl = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 0,
            types: vec![InductiveType {
                name: name.clone(),
                type_: Expr::sort(clean_kernel::level::Level::succ(
                    clean_kernel::level::Level::param(u),
                )),
                constructors: vec![Constructor {
                    name: Name::from_string("WS14PolyUnit.mk"),
                    type_: Expr::const_(
                        name.clone(),
                        vec![clean_kernel::level::Level::param(Name::from_string("u"))],
                    ),
                }],
            }],
        };
        env.add_inductive(decl).expect("WS14PolyUnit add_inductive");
        env
    }

    /// Level params are POSITIONAL binders: a shard copy whose params are
    /// alpha-renamed (`Eq.{u}` seeded vs `Eq.{u_1}` genuine olean spelling)
    /// denotes the same declaration and must be accepted.
    #[test]
    fn test_ws14_member_alpha_renamed_level_params_accepted() {
        use clean_kernel::level::Level;
        let env = env_with_ws14poly();
        let existing = env
            .get_const(&Name::from_string("WS14PolyUnit.rec"))
            .expect("synthesized WS14PolyUnit.rec");
        assert!(
            !existing.level_params.is_empty(),
            "fixture needs a level-polymorphic recursor"
        );
        // Rename every level param `n` -> `n_1` and rewrite the type to match.
        let renamed_params: Vec<Name> = existing
            .level_params
            .iter()
            .map(|n| Name::from_string(&format!("{n}_1")))
            .collect();
        let renamed_levels: Vec<Level> = renamed_params
            .iter()
            .map(|n| Level::param(n.clone()))
            .collect();
        let renamed_type = existing
            .type_
            .instantiate_level_params_direct(&existing.level_params, &renamed_levels);
        assert_ne!(
            renamed_type, existing.type_,
            "fixture must actually rename a level param occurrence"
        );
        let copy = ReconstructedConstant {
            decl_name: Name::from_string("WS14PolyUnit.rec"),
            decl_kind: DeclKind::Recursor,
            level_params: renamed_params,
            type_expr: renamed_type,
            value_expr: None,
        };
        let result = try_accept_existing_inductive_family_constant(&env, &copy);
        assert!(
            matches!(result, Some(AddConstResult::KernelVerified)),
            "alpha-renamed level params must be accepted, got {result:?}"
        );
    }

    /// Different level-param ARITY is a genuine mismatch and must still fail
    /// closed — alpha-insensitivity must not relax arity.
    #[test]
    fn test_ws14_member_wrong_level_arity_rejected() {
        let env = env_with_ws14poly();
        let existing = env
            .get_const(&Name::from_string("WS14PolyUnit.rec"))
            .expect("synthesized WS14PolyUnit.rec");
        let mut padded = existing.level_params.clone();
        padded.push(Name::from_string("v_extra"));
        let copy = ReconstructedConstant {
            decl_name: Name::from_string("WS14PolyUnit.rec"),
            decl_kind: DeclKind::Recursor,
            level_params: padded,
            type_expr: existing.type_.clone(),
            value_expr: None,
        };
        let result = try_accept_existing_inductive_family_constant(&env, &copy);
        match result {
            Some(AddConstResult::KernelRejected(msg)) => assert!(
                msg.contains("different level params"),
                "arity mismatch must cite level params, got {msg}"
            ),
            other => panic!("extra level param must be rejected, got {other:?}"),
        }
    }
}

/// Tests for the [`super::InductiveReplayPolicy`] that selects whether the
/// checked `add_inductive` family replay generates Clean's OWN convenience
/// definitions (`casesOn`/`recOn`/`noConfusion`/`noConfusionType`/…) or installs
/// only the kernel certificate (types/constructors/`rec`) and leaves the
/// convenience definitions to be carried from the source through `add_decl`.
///
/// This is the `.olean`-stamp fidelity fix: generating Clean's non-Lean-faithful
/// twins SHADOWS the shard's Lean-stored spellings, spuriously failing valid
/// downstream re-checks on universe/shape mismatches (the dominant
/// axiom_fallback `type_mismatch` tail). `LeanFaithful` avoids the shadow.
mod inductive_replay_policy_tests {
    use super::super::{verify_corpus_incremental_with_env_policy, InductiveReplayPolicy};
    use super::build_parameterized_inductive_replay_shard;
    use crate::library::MathverseLibrary;
    use crate::trust::policy::TrustPolicy;
    use clean_kernel::{Environment, Name};

    fn verify_replaylist(
        policy: InductiveReplayPolicy,
    ) -> (Environment, super::super::IncrementalVerifyReport) {
        // The parameterized `ReplayList` family — the same fixture the existing
        // `verify_shard_incremental` (default Generate) replay test uses. A FRESH
        // (empty) env, like that test: the family's prerequisites are all in the
        // shard.
        let shard = build_parameterized_inductive_replay_shard();
        let mut library = MathverseLibrary::new(TrustPolicy::permissive());
        library.load_shard(&shard).unwrap();
        verify_corpus_incremental_with_env_policy(&library, Environment::new(), policy)
    }

    /// `LeanFaithful` (the `.olean`-stamp policy) KernelVerifies the inductive
    /// family — the kernel certificate (type + constructors + `rec`) is installed
    /// through the SAME fully-checked `add_inductive_core` path. The fix must not
    /// regress the family's verdict; it only stops the convenience twins from
    /// being generated.
    #[test]
    fn test_lean_faithful_kernel_verifies_the_inductive_family() {
        let (_env, report) = verify_replaylist(InductiveReplayPolicy::LeanFaithful);
        assert_eq!(report.total, 3);
        assert_eq!(
            report.kernel_verified, 3,
            "the ReplayList family (type + 2 ctors) must KernelVerify under LeanFaithful; \
             failures = {:?}",
            report.failures
        );
        assert_eq!(report.failed, 0, "{:?}", report.failures);
    }

    /// `LeanFaithful` installs the kernel CERTIFICATE (the inductive type, its
    /// constructors, and `rec`) but does NOT synthesize Clean's convenience
    /// definitions (`casesOn`/`recOn`/`noConfusion`/`noConfusionType`). This pins
    /// both halves of the soundness/behavior contract:
    ///   - certificate present  => no kernel check is skipped (the family is
    ///     fully checked; only the *re-derivation* of convenience defs is left to
    ///     the source's own `add_decl`-checked spellings);
    ///   - convenience twins absent => no Clean-generated definition can shadow
    ///     the shard's Lean-stored spelling (the shadow that produced the
    ///     spurious universe `type_mismatch` on `Equiv.noConfusionType` /
    ///     `Equiv.mk.noConfusion`).
    #[test]
    fn test_lean_faithful_installs_certificate_without_convenience_twins() {
        let (env, _) = verify_replaylist(InductiveReplayPolicy::LeanFaithful);

        // Certificate present (fully kernel-checked).
        assert!(
            env.get_inductive(&Name::from_string("ReplayList"))
                .is_some(),
            "ReplayList"
        );
        assert!(
            env.get_constructor(&Name::from_string("ReplayList.nil"))
                .is_some(),
            "ReplayList.nil"
        );
        assert!(
            env.get_constructor(&Name::from_string("ReplayList.cons"))
                .is_some(),
            "ReplayList.cons"
        );
        assert!(
            env.get_recursor(&Name::from_string("ReplayList.rec"))
                .is_some(),
            "ReplayList.rec"
        );

        // Convenience twins NOT generated (left to the source via add_decl).
        assert!(
            env.get_const(&Name::from_string("ReplayList.casesOn"))
                .is_none(),
            "LeanFaithful must NOT synthesize ReplayList.casesOn"
        );
        assert!(
            env.get_const(&Name::from_string("ReplayList.noConfusionType"))
                .is_none(),
            "LeanFaithful must NOT synthesize ReplayList.noConfusionType (the shadow)"
        );
    }
}

// ---------------------------------------------------------------------------
// Nested-family restore acceptor tests (design
// designs/2026-07-02-parameterized-nested-inductives.md §4 + B3 replay
// contract). A NESTED family (RSyn | node : RCList RSyn → RSyn) post-restore
// registers `RSyn.rec_1` (the renamed aux recursor) in BOTH `constants` and
// `recursors` — the acceptor probes `get_const` FIRST, then `get_recursor`
// ([R4]). Shards carry `rec_1` as a separate DeclKind::Recursor constant, so
// per-constant replay must recognize it as the already-checked member.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod nested_family_restore_acceptor_tests {
    use super::super::{try_accept_existing_inductive_family_constant, AddConstResult};
    use crate::inductive_replay::ReconstructedConstant;
    use crate::types::DeclKind;
    use clean_kernel::expr::Expr;
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
    use clean_kernel::level::Level;
    use clean_kernel::{Environment, Name};

    /// Env with a List-shaped container `RCList.{u} : Type u → Type u` and
    /// the nested root `RSyn | leaf : RSyn | node : RCList RSyn → RSyn`.
    /// Post-restore the env holds RSyn in container spelling, RSyn.rec, and
    /// RSyn.rec_1 — no `_nested.*` names.
    fn env_with_nested_rsyn() -> Environment {
        let mut env = Environment::try_with_prelude().expect("prelude");
        let u = Name::from_string("u");
        let rclist = Name::from_string("RCList");
        let type_u = Expr::from_kind(clean_kernel::expr::ExprKind::Sort(Level::succ(
            Level::param(u.clone()),
        )));
        let rclist_at = |lvl: Level| Expr::const_(rclist.clone(), vec![lvl]);

        env.add_inductive(InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: rclist.clone(),
                type_: Expr::pi(
                    clean_kernel::expr::BinderInfo::Default,
                    type_u.clone(),
                    type_u.clone(),
                ),
                constructors: vec![
                    Constructor {
                        name: Name::from_string("RCList.nil"),
                        type_: Expr::pi(
                            clean_kernel::expr::BinderInfo::Default,
                            type_u.clone(),
                            Expr::app(rclist_at(Level::param(u.clone())), Expr::bvar(0)),
                        ),
                    },
                    Constructor {
                        name: Name::from_string("RCList.cons"),
                        type_: Expr::pi(
                            clean_kernel::expr::BinderInfo::Default,
                            type_u,
                            Expr::pi(
                                clean_kernel::expr::BinderInfo::Default,
                                Expr::bvar(0),
                                Expr::pi(
                                    clean_kernel::expr::BinderInfo::Default,
                                    Expr::app(rclist_at(Level::param(u.clone())), Expr::bvar(1)),
                                    Expr::app(rclist_at(Level::param(u.clone())), Expr::bvar(2)),
                                ),
                            ),
                        ),
                    },
                ],
            }],
        })
        .expect("RCList add_inductive");

        let rsyn = Name::from_string("RSyn");
        let rsyn_ref = Expr::const_(rsyn.clone(), vec![]);
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: rsyn.clone(),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: Name::from_string("RSyn.leaf"),
                        type_: rsyn_ref.clone(),
                    },
                    Constructor {
                        name: Name::from_string("RSyn.node"),
                        type_: Expr::pi(
                            clean_kernel::expr::BinderInfo::Default,
                            Expr::app(
                                Expr::const_(Name::from_string("RCList"), vec![Level::zero()]),
                                rsyn_ref.clone(),
                            ),
                            rsyn_ref,
                        ),
                    },
                ],
            }],
        })
        .expect("nested RSyn add_inductive (restore path)");
        env
    }

    fn recon_member(
        env: &Environment,
        name: &str,
        kind: DeclKind,
        type_expr: Expr,
    ) -> ReconstructedConstant {
        let level_params = env
            .get_const(&Name::from_string(name))
            .expect("member present in env")
            .level_params
            .clone();
        ReconstructedConstant {
            decl_name: Name::from_string(name),
            decl_kind: kind,
            level_params,
            type_expr,
            value_expr: None,
        }
    }

    /// THE [R4] pin: a shard copy of the renamed aux recursor `RSyn.rec_1`
    /// (DeclKind::Recursor, exact regenerated type) is recognized as the
    /// already-checked member — both the `get_const` and `get_recursor`
    /// probes hit.
    #[test]
    fn test_nested_rec_1_shard_copy_accepted() {
        let env = env_with_nested_rsyn();
        let rec_1 = Name::from_string("RSyn.rec_1");
        let rec_1_ty = env
            .get_const(&rec_1)
            .expect("RSyn.rec_1 must be registered as a constant [R4]")
            .type_
            .clone();
        assert!(
            env.get_recursor(&rec_1).is_some(),
            "RSyn.rec_1 must be registered in the recursor table [R4]"
        );
        let copy = recon_member(&env, "RSyn.rec_1", DeclKind::Recursor, rec_1_ty);
        let result = try_accept_existing_inductive_family_constant(&env, &copy);
        assert!(
            matches!(result, Some(AddConstResult::KernelVerified)),
            "exact-type rec_1 shard copy must be accepted, got {result:?}"
        );
    }

    /// Before any family install, a `rec_1` recon falls through (`None`) —
    /// the acceptor is not our case and the caller's skeleton rejection
    /// handles it.
    #[test]
    fn test_rec_1_before_family_install_falls_through() {
        let env = Environment::try_with_prelude().expect("prelude");
        let copy = ReconstructedConstant {
            decl_name: Name::from_string("RSyn.rec_1"),
            decl_kind: DeclKind::Recursor,
            level_params: vec![Name::from_string("u")],
            type_expr: Expr::type_(),
            value_expr: None,
        };
        let result = try_accept_existing_inductive_family_constant(&env, &copy);
        assert!(
            result.is_none(),
            "rec_1 with no installed family must fall through, got {result:?}"
        );
    }

    /// Wrong level params on the rec_1 copy: rejected closed.
    #[test]
    fn test_nested_rec_1_wrong_levels_rejected() {
        let env = env_with_nested_rsyn();
        let rec_1 = Name::from_string("RSyn.rec_1");
        let rec_1_ty = env.get_const(&rec_1).expect("rec_1 constant").type_.clone();
        let copy = ReconstructedConstant {
            decl_name: rec_1,
            decl_kind: DeclKind::Recursor,
            level_params: vec![Name::from_string("u"), Name::from_string("v")],
            type_expr: rec_1_ty,
            value_expr: None,
        };
        let result = try_accept_existing_inductive_family_constant(&env, &copy);
        assert!(
            matches!(result, Some(AddConstResult::KernelRejected(_))),
            "level-param mismatch must reject closed, got {result:?}"
        );
    }

    /// Post-restore env shape: no `_nested.*` constant is visible to the
    /// replay lane, and the family match surface (type + ctors + rec) is in
    /// container spelling.
    #[test]
    fn test_nested_family_env_shape_post_restore() {
        let env = env_with_nested_rsyn();
        assert!(
            env.get_const(&Name::from_string("_nested.RCList_1"))
                .is_none(),
            "no aux constant may survive restore"
        );
        let rsyn_val = env
            .get_inductive(&Name::from_string("RSyn"))
            .expect("RSyn registered");
        assert_eq!(
            rsyn_val.all_names,
            vec![Name::from_string("RSyn")],
            "all_names = originals only"
        );
        let rec = env
            .get_recursor(&Name::from_string("RSyn.rec"))
            .expect("RSyn.rec");
        assert_eq!(rec.num_motives, 2, "RSyn + the RCList mirror");
        assert_eq!(rec.num_minors, 4, "leaf, node, nil, cons");
        let rec_1 = env
            .get_recursor(&Name::from_string("RSyn.rec_1"))
            .expect("RSyn.rec_1");
        assert_eq!(rec_1.rules.len(), 2);
        assert_eq!(
            rec_1.rules[0].constructor_name,
            Name::from_string("RCList.nil"),
            "rules re-keyed to the real container ctors"
        );
        assert_eq!(
            rec_1.rules[1].constructor_name,
            Name::from_string("RCList.cons")
        );
    }
}

/// Tests for the seeded-duplicate dedup in `try_add_decl`
/// ([`super::try_accept_seeded_duplicate`]): a value-bearing shard constant
/// whose NAME already exists in the env (seeded prelude copy or earlier
/// replay) must be decided honestly — checked axiom-stub upgrade, twin
/// acceptance (env copy authoritative, nothing installed), or a PRECISE
/// fail-closed divergence rejection — instead of dying on `add_decl`'s
/// blanket "Duplicate declaration".
mod seeded_duplicate_dedup_tests {
    use super::super::{try_add_decl, AddConstResult};
    use crate::types::DeclKind;
    use clean_kernel::expr::Expr;
    use clean_kernel::level::Level;
    use clean_kernel::{Declaration, Environment, Name};

    fn n(s: &str) -> Name {
        Name::from_string(s)
    }

    /// An env with two Props and witnesses: `TwinP`, `TwinQ : Prop` (axioms),
    /// `twin_r`, `twin_r2 : TwinP`, `twin_s : TwinQ` (axioms).
    fn env_with_props() -> Environment {
        let mut env = Environment::new();
        for p in ["TwinP", "TwinQ"] {
            env.add_decl(Declaration::Axiom {
                name: n(p),
                level_params: vec![],
                type_: Expr::prop(),
            })
            .expect("register Prop");
        }
        for (w, p) in [
            ("twin_r", "TwinP"),
            ("twin_r2", "TwinP"),
            ("twin_s", "TwinQ"),
        ] {
            env.add_decl(Declaration::Axiom {
                name: n(w),
                level_params: vec![],
                type_: Expr::const_(n(p), vec![]),
            })
            .expect("register witness");
        }
        env
    }

    /// A seeded, kernel-checked theorem replayed VERBATIM from the shard must
    /// be accepted KernelVerified (twin; nothing installed).
    #[test]
    fn test_seeded_dup_identical_theorem_accepted_kernel_verified() {
        let mut env = env_with_props();
        env.add_decl(Declaration::Theorem {
            name: n("twin_t"),
            level_params: vec![],
            type_: Expr::const_(n("TwinP"), vec![]),
            value: Expr::const_(n("twin_r"), vec![]),
        })
        .expect("seed checked theorem twin_t : TwinP := twin_r");

        let value = Expr::const_(n("twin_r"), vec![]);
        let result = try_add_decl(
            &mut env,
            n("twin_t"),
            DeclKind::Theorem,
            vec![],
            Expr::const_(n("TwinP"), vec![]),
            Some(&value),
            false,
        );
        assert!(
            matches!(result, AddConstResult::KernelVerified),
            "an identical seeded theorem must be accepted, got {result:?}"
        );
        // Nothing installed: the seeded proof term stays authoritative.
        let ci = env.get_const(&n("twin_t")).expect("still present");
        assert_eq!(ci.value, Some(Expr::const_(n("twin_r"), vec![])));
    }

    /// Proof irrelevance: a theorem twin whose olean PROOF TERM differs from
    /// the seeded (checked) proof is still the same Prop statement — accepted
    /// on the type match alone, seeded proof stays authoritative.
    #[test]
    fn test_seeded_dup_theorem_different_proof_accepted_by_proof_irrelevance() {
        let mut env = env_with_props();
        env.add_decl(Declaration::Theorem {
            name: n("twin_t"),
            level_params: vec![],
            type_: Expr::const_(n("TwinP"), vec![]),
            value: Expr::const_(n("twin_r"), vec![]),
        })
        .expect("seed checked theorem");

        let other_proof = Expr::const_(n("twin_r2"), vec![]);
        let result = try_add_decl(
            &mut env,
            n("twin_t"),
            DeclKind::Theorem,
            vec![],
            Expr::const_(n("TwinP"), vec![]),
            Some(&other_proof),
            false,
        );
        assert!(
            matches!(result, AddConstResult::KernelVerified),
            "same-Prop theorem with a different proof term must be accepted, got {result:?}"
        );
        let ci = env.get_const(&n("twin_t")).expect("still present");
        assert_eq!(
            ci.value,
            Some(Expr::const_(n("twin_r"), vec![])),
            "the seeded proof must remain authoritative (nothing installed)"
        );
    }

    /// A definition twin spelled with alpha-renamed level params and a def-eq
    /// value must be accepted: level params are positional binders.
    #[test]
    fn test_seeded_dup_alpha_renamed_definition_with_defeq_value_accepted() {
        let mut env = Environment::new();
        let u = n("u");
        env.add_decl(Declaration::Definition {
            name: n("twin_d"),
            level_params: vec![u.clone()],
            type_: Expr::sort(Level::succ(Level::param(u.clone()))),
            value: Expr::sort(Level::param(u.clone())),
            is_reducible: false,
        })
        .expect("seed checked definition twin_d.{u} : Sort (u+1) := Sort u");

        let v = n("v");
        let value = Expr::sort(Level::param(v.clone()));
        let result = try_add_decl(
            &mut env,
            n("twin_d"),
            DeclKind::Definition,
            vec![v.clone()],
            Expr::sort(Level::succ(Level::param(v))),
            Some(&value),
            false,
        );
        assert!(
            matches!(result, AddConstResult::KernelVerified),
            "alpha-renamed def-eq definition twin must be accepted, got {result:?}"
        );
        let ci = env.get_const(&n("twin_d")).expect("still present");
        assert_eq!(
            ci.level_params,
            vec![u],
            "the seeded copy stays authoritative (nothing installed)"
        );
    }

    /// A definition twin whose VALUE genuinely diverges from the seeded copy
    /// must be rejected with the precise value-divergence message.
    #[test]
    fn test_seeded_dup_definition_divergent_value_rejected_precisely() {
        let mut env = Environment::new();
        // An opaque inhabitant of Sort 1 that is NOT def-eq to Prop.
        env.add_decl(Declaration::Axiom {
            name: n("TwinA"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("register TwinA : Sort 1");
        env.add_decl(Declaration::Definition {
            name: n("twin_e"),
            level_params: vec![],
            type_: Expr::type_(),
            value: Expr::prop(),
            is_reducible: false,
        })
        .expect("seed checked definition twin_e : Sort 1 := Prop");

        let divergent = Expr::const_(n("TwinA"), vec![]);
        let result = try_add_decl(
            &mut env,
            n("twin_e"),
            DeclKind::Definition,
            vec![],
            Expr::type_(),
            Some(&divergent),
            false,
        );
        match result {
            AddConstResult::KernelRejected(msg) => {
                assert!(
                    msg.contains("duplicate of seeded constant twin_e")
                        && msg.contains("value not definitionally equal"),
                    "divergent value must name the constant and the value divergence, got: {msg}"
                );
            }
            other => panic!("divergent definition value must fail closed, got {other:?}"),
        }
        // The seeded value must be untouched.
        let ci = env.get_const(&n("twin_e")).expect("still present");
        assert_eq!(ci.value, Some(Expr::prop()));
    }

    /// A duplicate whose declared TYPE diverges from the seeded copy must be
    /// rejected with the precise type-divergence message.
    #[test]
    fn test_seeded_dup_divergent_type_rejected_precisely() {
        let mut env = env_with_props();
        // Seeded value-free stub: twin_x : TwinP.
        env.add_decl(Declaration::Axiom {
            name: n("twin_x"),
            level_params: vec![],
            type_: Expr::const_(n("TwinP"), vec![]),
        })
        .expect("seed value-free stub twin_x : TwinP");

        // Olean copy declares a DIFFERENT type (Sort 1) with a value.
        let value = Expr::prop();
        let result = try_add_decl(
            &mut env,
            n("twin_x"),
            DeclKind::Definition,
            vec![],
            Expr::type_(),
            Some(&value),
            false,
        );
        match result {
            AddConstResult::KernelRejected(msg) => {
                assert!(
                    msg.contains("duplicate of seeded constant twin_x")
                        && msg.contains("type not definitionally equal"),
                    "divergent type must name the constant and the type divergence, got: {msg}"
                );
            }
            other => panic!("divergent type must fail closed, got {other:?}"),
        }
    }

    /// End-to-end axiom-stub upgrade: a seeded VALUE-FREE axiom replayed with a
    /// value-bearing, kernel-checkable copy must land the genuine value —
    /// KernelVerified AND the env constant now carries the value.
    #[test]
    fn test_seeded_dup_axiom_stub_upgrade_lands_checked_value() {
        let mut env = env_with_props();
        env.add_decl(Declaration::Axiom {
            name: n("twin_u"),
            level_params: vec![],
            type_: Expr::const_(n("TwinP"), vec![]),
        })
        .expect("seed value-free stub twin_u : TwinP");

        let value = Expr::const_(n("twin_r"), vec![]);
        let result = try_add_decl(
            &mut env,
            n("twin_u"),
            DeclKind::Theorem,
            vec![],
            Expr::const_(n("TwinP"), vec![]),
            Some(&value),
            false,
        );
        assert!(
            matches!(result, AddConstResult::KernelVerified),
            "checked stub upgrade must mint KernelVerified, got {result:?}"
        );
        let ci = env.get_const(&n("twin_u")).expect("still present");
        assert_eq!(
            ci.value,
            Some(Expr::const_(n("twin_r"), vec![])),
            "the genuine value must have LANDED in the env"
        );
    }

    /// A value-free seeded stub whose olean value FAILS kernel checking must be
    /// rejected fail-closed, carrying the real upgrade error — never accepted
    /// as a twin on the type match alone (that would launder the unproven stub
    /// into a KernelVerified verdict).
    #[test]
    fn test_seeded_dup_stub_with_failing_value_rejected_with_upgrade_error() {
        let mut env = env_with_props();
        env.add_decl(Declaration::Axiom {
            name: n("twin_y"),
            level_params: vec![],
            type_: Expr::const_(n("TwinP"), vec![]),
        })
        .expect("seed value-free stub twin_y : TwinP");

        // twin_s : TwinQ does NOT prove TwinP — the checked upgrade must fail.
        let bad_value = Expr::const_(n("twin_s"), vec![]);
        let result = try_add_decl(
            &mut env,
            n("twin_y"),
            DeclKind::Theorem,
            vec![],
            Expr::const_(n("TwinP"), vec![]),
            Some(&bad_value),
            false,
        );
        match result {
            AddConstResult::KernelRejected(msg) => {
                assert!(
                    msg.contains("duplicate of seeded constant twin_y")
                        && msg.contains("checked stub upgrade failed"),
                    "failed stub upgrade must fail closed with the upgrade error, got: {msg}"
                );
            }
            other => panic!("ill-typed stub upgrade must fail closed, got {other:?}"),
        }
        let ci = env.get_const(&n("twin_y")).expect("stub still present");
        assert!(ci.value.is_none(), "stub must remain value-free");
    }

    /// Both sides value-free: a twin of the seeded axiom is exactly what the
    /// collision-free replay of this valueless row would have minted —
    /// AxiomFallback(None), never a proof-check verdict.
    #[test]
    fn test_seeded_dup_valueless_twin_of_axiom_is_axiom_fallback() {
        let mut env = env_with_props();
        env.add_decl(Declaration::Axiom {
            name: n("twin_z"),
            level_params: vec![],
            type_: Expr::const_(n("TwinP"), vec![]),
        })
        .expect("seed value-free stub twin_z : TwinP");

        let result = try_add_decl(
            &mut env,
            n("twin_z"),
            DeclKind::Theorem,
            vec![],
            Expr::const_(n("TwinP"), vec![]),
            None,
            false,
        );
        assert!(
            matches!(result, AddConstResult::AxiomFallback(None)),
            "a valueless twin of a value-free axiom must mint AxiomFallback(None), got {result:?}"
        );
    }
}

/// Axiom-kind seeded-duplicate handling
/// ([`super::try_accept_seeded_axiom_twin`]): a valueless `Axiom`/`Quot` shard
/// row whose NAME already exists in the env (the foundational seeds — `Quot`
/// primitives, `Quot.sound`, `propext`, `Classical.choice`, `sorryAx`) must be
/// decided honestly by a TYPE-ONLY twin compare instead of dying on
/// `add_decl`'s blanket "Duplicate declaration" (carrier-parity design P0,
/// Q1 — `designs/2026-07-03-carrier-types-bitvec-parity.md` §9).
mod seeded_axiom_twin_tests {
    use super::super::{try_accept_seeded_axiom_twin, AddConstResult};
    use clean_kernel::expr::Expr;
    use clean_kernel::level::Level;
    use clean_kernel::{Declaration, Environment, Name};

    fn n(s: &str) -> Name {
        Name::from_string(s)
    }

    /// A type-matched axiom twin of a seeded axiom is accepted as
    /// `AxiomAccepted` — the exact verdict a collision-free replay of the
    /// valueless row would have minted — and installs nothing.
    #[test]
    fn test_axiom_twin_type_match_accepted_axiom_accepted() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: n("twin_propext"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("seed axiom twin_propext : Prop");

        let result = try_accept_seeded_axiom_twin(&env, &n("twin_propext"), &[], &Expr::prop());
        assert!(
            matches!(result, AddConstResult::AxiomAccepted),
            "type-matched axiom twin must mint AxiomAccepted, got {result:?}"
        );
        let ci = env.get_const(&n("twin_propext")).expect("still present");
        assert_eq!(
            ci.value, None,
            "nothing installed; seeded copy authoritative"
        );
    }

    /// Level params are positional binders: an alpha-renamed twin matches.
    #[test]
    fn test_axiom_twin_alpha_renamed_level_params_accepted() {
        let mut env = Environment::new();
        let u = n("u");
        env.add_decl(Declaration::Axiom {
            name: n("twin_choice"),
            level_params: vec![u.clone()],
            type_: Expr::sort(Level::succ(Level::param(u))),
        })
        .expect("seed axiom twin_choice.{u} : Sort (u+1)");

        let v = n("v");
        let result = try_accept_seeded_axiom_twin(
            &env,
            &n("twin_choice"),
            std::slice::from_ref(&v),
            &Expr::sort(Level::succ(Level::param(v.clone()))),
        );
        assert!(
            matches!(result, AddConstResult::AxiomAccepted),
            "alpha-renamed axiom twin must be accepted, got {result:?}"
        );
    }

    /// A divergent TYPE is a real conflict: fail closed with the precise
    /// axiom-type divergence message.
    #[test]
    fn test_axiom_twin_divergent_type_rejected_precisely() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: n("twin_sorry"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("seed axiom twin_sorry : Prop");

        let result = try_accept_seeded_axiom_twin(&env, &n("twin_sorry"), &[], &Expr::type_());
        match result {
            AddConstResult::KernelRejected(msg) => {
                assert!(
                    msg.contains("duplicate of seeded constant twin_sorry")
                        && msg.contains("axiom type not definitionally equal"),
                    "divergent axiom type must name the constant and the divergence, got: {msg}"
                );
            }
            other => panic!("divergent axiom type must fail closed, got {other:?}"),
        }
    }

    /// A level-param arity mismatch is a real conflict: fail closed naming
    /// both arities.
    #[test]
    fn test_axiom_twin_arity_mismatch_rejected_precisely() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: n("twin_quot"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("seed axiom twin_quot : Prop");

        let result = try_accept_seeded_axiom_twin(&env, &n("twin_quot"), &[n("u")], &Expr::prop());
        match result {
            AddConstResult::KernelRejected(msg) => {
                assert!(
                    msg.contains("duplicate of seeded constant twin_quot")
                        && msg.contains("level-param arity 1 differs from seeded arity 0"),
                    "arity mismatch must name both arities, got: {msg}"
                );
            }
            other => panic!("arity mismatch must fail closed, got {other:?}"),
        }
    }

    /// An axiom twin of a seeded VALUE-BEARING (checked) definition of the
    /// same type: the env copy is strictly stronger; the axiom claim is
    /// accepted as `AxiomAccepted` (never a proof-check verdict for the row,
    /// and nothing installed).
    #[test]
    fn test_axiom_twin_of_checked_definition_accepted_axiom_accepted() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Definition {
            name: n("twin_def"),
            level_params: vec![],
            type_: Expr::type_(),
            value: Expr::prop(),
            is_reducible: false,
        })
        .expect("seed checked definition twin_def : Sort 1 := Prop");

        let result = try_accept_seeded_axiom_twin(&env, &n("twin_def"), &[], &Expr::type_());
        assert!(
            matches!(result, AddConstResult::AxiomAccepted),
            "axiom twin of a checked def must mint AxiomAccepted, got {result:?}"
        );
        let ci = env.get_const(&n("twin_def")).expect("still present");
        assert_eq!(
            ci.value,
            Some(Expr::prop()),
            "the seeded checked value must remain authoritative"
        );
    }
}

// ---------------------------------------------------------------------------
// Env-gated speculative-rejection capture (`CLEAN_SPECULATIVE_REJECT_LOG`)
//
// The speculative fail-closed discipline DISCARDS the kernel's rejection by
// design (a wrong motive guess reverts to a clean type-only axiom), which
// makes the reject reasons invisible. The capture instrument appends one
// `name<TAB>tag<TAB>detail` line per event to the env-named file — pure
// observation, verdicts byte-identical either way.
// ---------------------------------------------------------------------------
mod speculative_reject_log_tests {
    use super::super::{
        verify_shard_incremental, REJECT_TAG_FORCED_TYPE_ONLY, REJECT_TAG_MASKED_SEED,
        REJECT_TAG_MASKED_SEED_DEPS, REJECT_TAG_SPECULATIVE, SPECULATIVE_REJECT_LOG_ENV,
    };
    use crate::shard::{ShardReader, ShardWriter};
    use crate::types::{
        AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader,
        SourceSystem,
    };
    use clean_kernel::flat::{FlatExpr, FlatLevel};
    use std::sync::Mutex;

    /// Env vars are process-global: serialize the tests that set/unset
    /// `CLEAN_SPECULATIVE_REJECT_LOG` so they cannot race each other.
    static ENV_LOCK: Mutex<()> = Mutex::new(());

    /// Both silent lanes in one tiny synthetic corpus:
    /// - `P : Prop`                    (axiom carrier)
    /// - `B : P := (λ x:P, x)`         (NON-speculative masked failure → taint seed)
    /// - `S : P := B`                  (SPECULATIVE, deps rest on tainted `B` →
    ///                                  FORCED type-only before the kernel runs)
    /// - `SR : P := (λ x:P, x)`        (SPECULATIVE, taint-free, kernel REJECTS the
    ///                                  value → clean AxiomFallback(None), the
    ///                                  discarded-error lane)
    fn build_speculative_capture_shard() -> ShardReader {
        let mut writer = ShardWriter::new();
        let l0 = writer.add_level(FlatLevel::zero());
        let sort_prop = writer.add_expr(FlatExpr::sort(l0));

        let p_name = writer.add_string("P");
        let b_name = writer.add_string("B");
        let s_name = writer.add_string("S");
        let sr_name = writer.add_string("SR");

        let p_const = writer.add_expr(FlatExpr::const_ref(p_name, u32::MAX));
        let bvar0 = writer.add_expr(FlatExpr::bvar(0));
        // λ (x : P), x — has type `P → P`, never `P`: the kernel rejects it.
        let lam_p = writer.add_expr(FlatExpr::lam(0, p_const, bvar0));
        let b_const = writer.add_expr(FlatExpr::const_ref(b_name, u32::MAX));

        let mk = |name_idx, value_idx, profile: AxiomProfile| MathverseConstantHeader {
            name_idx,
            type_idx: p_const,
            value_idx,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::Translated as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Theorem as u8,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        // P : Prop (axiom carrier; type_idx overridden to Sort 0).
        writer.add_constant(MathverseConstantHeader {
            name_idx: p_name,
            type_idx: sort_prop,
            value_idx: crate::types::NO_VALUE,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::Translated as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Axiom as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        writer.add_constant(mk(b_name, lam_p, AxiomProfile::NONE));
        writer.add_constant(mk(s_name, b_const, AxiomProfile::SPECULATIVE_MOTIVE));
        writer.add_constant(mk(sr_name, lam_p, AxiomProfile::SPECULATIVE_MOTIVE));

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        ShardReader::from_bytes(&buf).unwrap()
    }

    /// Gating contract in one deterministic sequence (env vars are
    /// process-global, so both halves live in a single test): unset → no file
    /// is ever created; set → both lanes appear, and the verify verdicts are
    /// IDENTICAL either way (capture is observation only).
    #[test]
    fn test_speculative_reject_log_unset_no_file_set_captures_both_lanes() {
        let _guard = ENV_LOCK.lock().unwrap_or_else(|poison| poison.into_inner());
        let dir = tempfile::tempdir().expect("tempdir");
        let log_path = dir.path().join("rejects.tsv");
        let reader = build_speculative_capture_shard();

        // (1) Unset: capture fully disabled, no file created. The guard restores
        // the ambient value on scope exit.
        let _g_unset = crate::process_env::ScopedEnvVar::unset(SPECULATIVE_REJECT_LOG_ENV);
        let baseline = verify_shard_incremental(&reader);
        assert!(
            !log_path.exists(),
            "capture must not create a file when {SPECULATIVE_REJECT_LOG_ENV} is unset"
        );

        // (2) Set: identical replay, lines appear for both lanes. Scoped so the
        // var reverts to unset immediately after the captured replay.
        let captured = {
            let _g_set = crate::process_env::ScopedEnvVar::set(
                SPECULATIVE_REJECT_LOG_ENV,
                &log_path.to_string_lossy(),
            );
            verify_shard_incremental(&reader)
        };

        // Observation only: every verdict count is byte-identical.
        assert_eq!(baseline.kernel_verified, captured.kernel_verified);
        assert_eq!(baseline.axiom_accepted, captured.axiom_accepted);
        assert_eq!(baseline.axiom_fallback, captured.axiom_fallback);
        assert_eq!(baseline.failed, captured.failed);
        assert_eq!(baseline.axiom_fallback_names, captured.axiom_fallback_names);

        let contents =
            std::fs::read_to_string(&log_path).expect("capture file must exist when env is set");
        // Concurrent tests could in principle append their own lines (the env
        // var is process-global while set); assert on OUR names only.
        let lines: Vec<Vec<&str>> = contents
            .lines()
            .map(|l| l.split('\t').collect::<Vec<_>>())
            .collect();

        let sr = lines
            .iter()
            .find(|f| f.first() == Some(&"SR"))
            .expect("speculative kernel rejection of SR must be captured");
        assert_eq!(sr.get(1), Some(&REJECT_TAG_SPECULATIVE), "SR tag");
        assert!(
            sr.get(2).is_some_and(|d| !d.is_empty()),
            "SR must carry the kernel's error text, got {sr:?}"
        );

        let s = lines
            .iter()
            .find(|f| f.first() == Some(&"S"))
            .expect("forced type-only withhold of S must be captured");
        assert_eq!(s.get(1), Some(&REJECT_TAG_FORCED_TYPE_ONLY), "S tag");
        assert!(
            s.get(2).is_some_and(|d| d.contains('B')),
            "S's detail must name the tainted dependency B, got {s:?}"
        );

        // The non-speculative masked failure B is ALSO captured (the
        // MASKED_SEED census lane, 2026-07-12): one line with its own kernel
        // error and one companion line with the dependency-shape evidence.
        // Its error still surfaces in axiom_fallback_names — the capture is
        // observation only (verdict equality asserted above).
        let b = lines
            .iter()
            .find(|f| f.first() == Some(&"B") && f.get(1) == Some(&REJECT_TAG_MASKED_SEED))
            .expect("masked seed B must be captured under MASKED_SEED");
        assert!(
            b.get(2).is_some_and(|d| d.contains("Type mismatch")),
            "B's MASKED_SEED line must carry the kernel's error text, got {b:?}"
        );
        let b_deps = lines
            .iter()
            .find(|f| f.first() == Some(&"B") && f.get(1) == Some(&REJECT_TAG_MASKED_SEED_DEPS))
            .expect("masked seed B must carry a MASKED_SEED_DEPS evidence line");
        assert!(
            b_deps
                .get(2)
                .is_some_and(|d| d.contains("dt=0") && d.contains("transitive_standins=[]")),
            "B has no tainted deps and no stand-in reach in this fixture, got {b_deps:?}"
        );
    }

    /// A detail longer than the truncation bound is flattened to one line and
    /// cut at the bound (the TSV must stay one record per line).
    #[test]
    fn test_speculative_reject_log_truncates_and_flattens_detail() {
        let _guard = ENV_LOCK.lock().unwrap_or_else(|poison| poison.into_inner());
        let dir = tempfile::tempdir().expect("tempdir");
        let log_path = dir.path().join("trunc.tsv");
        let long = format!("head\tof\nerror {}", "x".repeat(2000));
        crate::process_env::with_serialized_env_vars(
            &[(SPECULATIVE_REJECT_LOG_ENV, &log_path.to_string_lossy())],
            || super::super::log_speculative_capture("C", REJECT_TAG_SPECULATIVE, &long),
        );

        let contents = std::fs::read_to_string(&log_path).expect("capture file written");
        let line = contents
            .lines()
            .find(|l| l.starts_with("C\t"))
            .expect("captured line for C");
        let fields: Vec<&str> = line.split('\t').collect();
        assert_eq!(fields.len(), 3, "flattened to exactly 3 TSV fields: {line}");
        assert!(
            fields[2].starts_with("head of error"),
            "control chars become spaces: {line}"
        );
        assert_eq!(
            fields[2].chars().count(),
            super::super::REJECT_DETAIL_MAX_CHARS + 3, // +3 for the "..." marker
            "detail truncated at the bound: {line}"
        );
    }
}

// ---------------------------------------------------------------------------
// types_eq_modulo_universe — the universe-collapse reconstruction-gap classifier
// ---------------------------------------------------------------------------

/// A pure `Sort`-level difference is universe-only.
#[test]
fn test_types_eq_modulo_universe_sort_levels_differ() {
    let s0 = Expr::sort(Level::zero());
    let s1 = Expr::sort(Level::succ(Level::zero()));
    let s2 = Expr::sort(Level::succ(Level::succ(Level::zero())));
    assert!(types_eq_modulo_universe(&s0, &s1));
    assert!(types_eq_modulo_universe(&s1, &s2));
    assert!(types_eq_modulo_universe(&s0, &s0));
}

/// The measured `injective2` / `big_nil` shape: two Pi types identical except a
/// single inner codomain `Sort` at a different level — universe-only.
#[test]
fn test_types_eq_modulo_universe_inner_sort_only() {
    let bd = clean_kernel::expr::BinderData::default();
    let dom = Expr::sort(Level::succ(Level::zero()));
    // Pi (_ : Type0), Prop      vs     Pi (_ : Type0), Type0
    let pi_prop = Expr::pi(bd, dom.clone(), Expr::sort(Level::zero()));
    let pi_type0 = Expr::pi(bd, dom, Expr::sort(Level::succ(Level::zero())));
    assert!(
        types_eq_modulo_universe(&pi_prop, &pi_type0),
        "Pi differing only in the codomain universe level is universe-only"
    );
}

/// NEGATIVE CONTROLS: any non-universe structural divergence is NOT universe-only,
/// so a genuine wrong-proof mismatch is never laundered into a clean stand-in.
#[test]
fn test_types_eq_modulo_universe_negative_controls() {
    let bd = clean_kernel::expr::BinderData::default();
    // Different Const NAME (levels ignored, but the name is load-bearing).
    assert!(
        !types_eq_modulo_universe(
            &Expr::const_str("mathcomp.A"),
            &Expr::const_str("mathcomp.B")
        ),
        "different Const names must NOT be universe-only"
    );
    // Different BVar index (a wrong de Bruijn reference is a real error).
    assert!(!types_eq_modulo_universe(&Expr::bvar(0), &Expr::bvar(1)));
    // Different structure: App vs Pi.
    let app = Expr::app(Expr::const_str("f"), Expr::bvar(0));
    let pi = Expr::pi(bd, Expr::sort(Level::zero()), Expr::bvar(0));
    assert!(!types_eq_modulo_universe(&app, &pi));
    // Same shape, but a Const name differs DEEP inside (App argument).
    let app_a = Expr::app(Expr::const_str("f"), Expr::const_str("A"));
    let app_b = Expr::app(Expr::const_str("f"), Expr::const_str("B"));
    assert!(
        !types_eq_modulo_universe(&app_a, &app_b),
        "a deep Const-name divergence must surface as non-universe-only"
    );
    // A Sort-level difference does NOT rescue an otherwise structural mismatch:
    // Sort vs a non-Sort term is not universe-only.
    assert!(!types_eq_modulo_universe(
        &Expr::sort(Level::zero()),
        &Expr::bvar(0)
    ));
}

/// The `is_universe_collapse_rejection` classifier over a reconstructed
/// `EnvError` — the exact `big_nil` shape (`TypeCheckFailed{TypeMismatch{Sort,
/// Sort}}`) must be recognized, and a structural mismatch must NOT be.
#[test]
fn test_is_universe_collapse_rejection() {
    use clean_kernel::{KernelEnvError, KernelTypeError};
    let sort_mismatch = KernelEnvError::TypeCheckFailed {
        name: Name::from_string("mathcomp.ssreflect.bigop.big_nil"),
        source: KernelTypeError::TypeMismatch {
            expected: Box::new(Expr::sort(Level::succ(Level::zero()))),
            inferred: Box::new(Expr::sort(Level::succ(Level::succ(Level::zero())))),
            location: None,
        },
    };
    assert!(
        is_universe_collapse_rejection(&sort_mismatch),
        "a pure Sort-level TypeMismatch must classify as universe-collapse"
    );
    // NEGATIVE CONTROL: a genuine structural mismatch (different Const names)
    // must NOT be laundered.
    let structural = KernelEnvError::TypeCheckFailed {
        name: Name::from_string("x"),
        source: KernelTypeError::TypeMismatch {
            expected: Box::new(Expr::const_str("A")),
            inferred: Box::new(Expr::const_str("B")),
            location: None,
        },
    };
    assert!(!is_universe_collapse_rejection(&structural));
    // NEGATIVE CONTROL: a non-TypeMismatch error is never universe-collapse.
    let other = KernelEnvError::UnknownInductive(Name::from_string("Foo"));
    assert!(!is_universe_collapse_rejection(&other));
}

// ---------------------------------------------------------------------------
// is_int63_primitive_stuck_rejection — the native-primitive-stuck classifier
// (a value rejection whose only obstruction is a value-less int63/float/array/
// string machine primitive Clean's kernel cannot reduce → clean type-only
// stand-in, no masked-failure taint).
// ---------------------------------------------------------------------------

/// Register a VALUE-LESS native-primitive axiom `PrimInt63.add : Nat→Nat→Nat`
/// in a prelude env, plus a value-BEARING helper in the same module, and return
/// `(env, add, nat, zero)` for building stuck-conversion mismatches.
fn env_with_native_int63_primitive() -> (Environment, Expr, Expr, Expr) {
    use clean_kernel::expr::BinderInfo;
    let mut env = Environment::try_with_prelude().expect("prelude env");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_bin = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
    );
    // The native machine op — value-less axiom, no reduction rule (STUCK).
    let add_name = Name::from_string("Coq.Numbers.Cyclic.Int63.PrimInt63.add");
    env.add_decl(Declaration::Axiom {
        name: add_name.clone(),
        level_params: vec![],
        type_: nat_bin.clone(),
    })
    .expect("register native primitive axiom");
    // A DEFINED helper in the same primitive module (`PrimInt63.id_int`-shaped):
    // it DOES reduce, so it must NOT be treated as a stuck primitive.
    let id_name = Name::from_string("Coq.Numbers.Cyclic.Int63.PrimInt63.id_int");
    env.add_decl(Declaration::Definition {
        name: id_name,
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
        value: Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
        is_reducible: true,
    })
    .expect("register defined helper");
    let add = Expr::const_(add_name, vec![]);
    (env, add, nat, zero)
}

/// Build `@Eq.{1} Nat lhs rhs`.
fn eq_nat(nat: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    Expr::app(
        Expr::app(Expr::app(eq, nat.clone()), lhs.clone()),
        rhs.clone(),
    )
}

fn typecheck_mismatch(expected: Expr, inferred: Expr) -> clean_kernel::KernelEnvError {
    clean_kernel::KernelEnvError::TypeCheckFailed {
        name: Name::from_string("Test.int63_stuck"),
        source: clean_kernel::KernelTypeError::TypeMismatch {
            expected: Box::new(expected),
            inferred: Box::new(inferred),
            location: None,
        },
    }
}

/// `is_stuck_native_primitive` is BOTH namespace- AND value-less-gated: the
/// value-less op in the primitive module is stuck; the DEFINED helper in the
/// same module and a value-less axiom OUTSIDE the module are not.
#[test]
fn test_is_stuck_native_primitive_namespace_and_valueless_gated() {
    let (env, _add, _nat, _zero) = env_with_native_int63_primitive();
    assert!(
        is_stuck_native_primitive(
            &env,
            &Name::from_string("Coq.Numbers.Cyclic.Int63.PrimInt63.add")
        ),
        "value-less op in the primitive module is a stuck native primitive"
    );
    assert!(
        !is_stuck_native_primitive(
            &env,
            &Name::from_string("Coq.Numbers.Cyclic.Int63.PrimInt63.id_int")
        ),
        "a DEFINED helper in the primitive module reduces — not stuck"
    );
    // A value-less axiom OUTSIDE any primitive module (e.g. a genuine Coq
    // axiom) is NOT a native primitive — must not be laundered.
    assert!(
        !is_stuck_native_primitive(&env, &Name::from_string("Classical.choice")),
        "a value-less axiom outside the primitive modules is not a native primitive"
    );
}

/// A value `TypeMismatch` whose divergence is a stuck value-less native
/// primitive (`add 0 0` on one side, `0` on the other) classifies int63-stuck:
/// the proof appeals to native machine computation Clean cannot perform.
#[test]
fn test_int63_primitive_stuck_rejection_positive() {
    let (env, add, nat, zero) = env_with_native_int63_primitive();
    // add 0 0 — a value-less-const application, STUCK (no reduction rule).
    let add00 = Expr::app(Expr::app(add, zero.clone()), zero.clone());
    // `@Eq Nat (add 0 0) 0` (expected) vs `@Eq Nat (add 0 0) (add 0 0)`
    // (inferred, an `eq_refl (add 0 0)` proof): the 3rd argument diverges, and
    // the inferred side there is stuck on `add`.
    let err = typecheck_mismatch(eq_nat(&nat, &add00, &zero), eq_nat(&nat, &add00, &add00));
    assert!(
        is_int63_primitive_stuck_rejection(&env, &err),
        "a mismatch whose only obstruction is a stuck native primitive must classify int63-stuck"
    );
}

/// The `Uint63.to_Z 0` / `succ_spec` shape: the divergent sub-term whnf-reduces
/// to a RECURSOR stuck on a native-primitive SCRUTINEE (the primitive is nested
/// as an argument of the irreducible `Nat.rec`, not at its head). The deep scan
/// through the stuck spine must still classify int63-stuck.
#[test]
fn test_int63_primitive_stuck_rejection_recursor_stuck_on_primitive_scrutinee() {
    use clean_kernel::expr::BinderInfo;
    let (env, add, nat, zero) = env_with_native_int63_primitive();
    // Major premise `add 0 0` — STUCK (value-less primitive), so `Nat.rec` over
    // it cannot iota-reduce and whnf leaves it as `Nat.rec … (add 0 0)`, headed
    // by the recursor with the primitive buried in an argument.
    let add00 = Expr::app(Expr::app(add, zero.clone()), zero.clone());
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone()); // λ _:Nat, Nat
    let succ_minor = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
    ); // λ _ ih, ih
    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let stuck = Expr::app(
        Expr::app(
            Expr::app(Expr::app(nat_rec, motive), zero.clone()),
            succ_minor,
        ),
        add00,
    );
    // `@Eq Nat (Nat.rec … (add 0 0)) 0` (expected) vs `@Eq Nat 0 0` (inferred):
    // the divergence is the stuck recursor vs `0`.
    let err = typecheck_mismatch(eq_nat(&nat, &stuck, &zero), eq_nat(&nat, &zero, &zero));
    assert!(
        is_int63_primitive_stuck_rejection(&env, &err),
        "a recursor stuck on a native-primitive scrutinee must classify int63-stuck"
    );
}

/// NEGATIVE CONTROL (the soundness pin): a GENUINE wrong proof — a `0 = 1`
/// mismatch with NO primitive anywhere — must STAY a masked seed, never
/// laundered into a clean stand-in.
#[test]
fn test_int63_primitive_stuck_rejection_negative_genuine_wrong_proof() {
    let (env, _add, nat, zero) = env_with_native_int63_primitive();
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );
    // `@Eq Nat 0 0` (expected) vs `@Eq Nat 0 1` (inferred): the divergence is
    // `0` vs `1`, two Nat constructors — no stuck primitive to blame.
    let err = typecheck_mismatch(eq_nat(&nat, &zero, &zero), eq_nat(&nat, &zero, &one));
    assert!(
        !is_int63_primitive_stuck_rejection(&env, &err),
        "a genuine wrong proof (0 vs 1, no primitive) must stay a masked seed"
    );
}

/// NEGATIVE CONTROL: a rejection STUCK on a value-less axiom that is NOT a
/// native primitive (a genuine opaque Coq axiom outside the primitive modules)
/// must NOT be laundered — only true native primitives are out-of-model.
#[test]
fn test_int63_primitive_stuck_rejection_negative_non_primitive_stuck_axiom() {
    use clean_kernel::expr::BinderInfo;
    let (mut env, _add, nat, zero) = env_with_native_int63_primitive();
    // A value-less axiom `Some.Ordinary.opaque : Nat→Nat` — stuck under
    // reduction, but NOT a machine primitive (wrong namespace).
    let opaque_name = Name::from_string("Some.Ordinary.opaque");
    env.add_decl(Declaration::Axiom {
        name: opaque_name.clone(),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
    })
    .expect("register non-primitive opaque axiom");
    let op0 = Expr::app(Expr::const_(opaque_name, vec![]), zero.clone());
    let err = typecheck_mismatch(eq_nat(&nat, &op0, &zero), eq_nat(&nat, &op0, &op0));
    assert!(
        !is_int63_primitive_stuck_rejection(&env, &err),
        "a stuck NON-primitive opaque axiom is not native machine computation — must stay masked"
    );
}

/// NEGATIVE CONTROL: a non-`TypeMismatch` kernel error is never int63-stuck.
#[test]
fn test_int63_primitive_stuck_rejection_negative_non_mismatch() {
    let (env, _add, _nat, _zero) = env_with_native_int63_primitive();
    let err = clean_kernel::KernelEnvError::UnknownInductive(Name::from_string("Foo"));
    assert!(!is_int63_primitive_stuck_rejection(&env, &err));
}

/// PRECISION under the syntactic pre-filter: a mismatch whose types DO name a
/// primitive-bearing constant (so the pre-filter admits it) but whose actual
/// DIVERGENCE is an ordinary, non-primitive term (`0` vs `1`, with the shared
/// `add 0 0` matching on both sides) must STILL stay a masked seed. This pins
/// that the reconcile logic — not merely the pre-filter — enforces the
/// localization: a primitive mentioned in a SHARED part never launders a
/// genuine divergence elsewhere.
#[test]
fn test_int63_primitive_stuck_rejection_negative_primitive_shared_divergence_ordinary() {
    let (env, add, nat, zero) = env_with_native_int63_primitive();
    let add00 = Expr::app(Expr::app(add, zero.clone()), zero.clone());
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );
    // `@Eq Nat (add 0 0) 0` vs `@Eq Nat (add 0 0) 1`: the `add 0 0` matches on
    // both sides; the genuine divergence is `0` vs `1`.
    let err = typecheck_mismatch(eq_nat(&nat, &add00, &zero), eq_nat(&nat, &add00, &one));
    assert!(
        !is_int63_primitive_stuck_rejection(&env, &err),
        "a primitive in a SHARED sub-term must not launder a genuine 0-vs-1 divergence"
    );
}

/// The syntactic pre-filter admits a type that names a primitive-bearing
/// constant (an int63 wrapper like `Uint63.to_Z`) and rejects one that does not.
#[test]
fn test_mentions_primitive_bearing_const_gates_on_int63_family() {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    // `Uint63.to_Z 0` — names an int63-family wrapper.
    let to_z = Expr::const_(
        Name::from_string("Coq.Numbers.Cyclic.Int63.Uint63.to_Z"),
        vec![],
    );
    assert!(mentions_primitive_bearing_const(&Expr::app(
        to_z,
        zero.clone()
    )));
    // A pure `Nat.succ 0` names nothing primitive-bearing.
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    assert!(!mentions_primitive_bearing_const(&Expr::app(succ, zero)));
    assert!(!mentions_primitive_bearing_const(&nat));
}

// ---------------------------------------------------------------------------
// Monotone motive-universe retry (Set-valued spec elimination)
// ---------------------------------------------------------------------------

/// `is_concrete_level_numeral` recognises exactly the `Succ^n(Zero)` shape that
/// `cic_to_flat_expr` emits for a recursor motive-universe instance; algebraic
/// levels are excluded (they are already-correct polymorphic instances).
#[test]
fn test_is_concrete_level_numeral_only_matches_succ_zero_chains() {
    assert!(is_concrete_level_numeral(&Level::zero()));
    assert!(is_concrete_level_numeral(&Level::succ(Level::zero())));
    assert!(is_concrete_level_numeral(&Level::succ(Level::succ(
        Level::zero()
    ))));
    assert!(!is_concrete_level_numeral(&Level::Param(
        Name::from_string("u")
    )));
    assert!(!is_concrete_level_numeral(&Level::max(
        Level::zero(),
        Level::Param(Name::from_string("u")),
    )));
}

/// `bump_recursor_motive_levels` bumps ONLY a `<…>.rec` instance carrying a
/// single concrete-numeral level, leaves every other node untouched, and
/// returns `None` when the term carries no such recursor (nothing to retry).
#[test]
fn test_bump_recursor_motive_levels_targets_recursor_consts_only() {
    use clean_kernel::expr::ExprKind as K;
    let rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let app = Expr::app(rec0, zero.clone());
    let bumped = bump_recursor_motive_levels(&app).expect("a recursor instance is present");
    match bumped.kind() {
        K::App(f, a) => {
            match f.kind() {
                K::Const(name, levels) => {
                    assert_eq!(name.last_component().as_deref(), Some("rec"));
                    assert_eq!(levels.len(), 1);
                    // The instance went 0 -> 1 (one `Succ` wrapper).
                    assert!(matches!(&levels[0], Level::Succ(_)));
                }
                other => panic!("expected the recursor const head, got {other:?}"),
            }
            // The non-recursor argument is left exactly as-is.
            assert!(matches!(a.kind(), K::Const(_, _)));
        }
        other => panic!("expected an App, got {other:?}"),
    }
    // No recursor instance anywhere -> None (the retry never fires).
    assert!(bump_recursor_motive_levels(&zero).is_none());
    // A recursor at a non-numeral (polymorphic) level is left untouched -> None.
    let rec_param = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::Param(Name::from_string("u"))],
    );
    assert!(bump_recursor_motive_levels(&rec_param).is_none());
}

/// End-to-end soundness for the monotone retry on a REAL Set-valued
/// elimination: `Nat.rec` with the motive `λ _:Nat, Nat` returns the TYPE
/// `Nat : Sort 1`, so `Nat.rec.{0}` is kernel-REJECTED on the motive universe,
/// exactly the leqP-family shape (a spec inductive is `Set`-valued). The retry
/// bumps the instance to `{1}` and the kernel accepts it — AND the accepted
/// value still COMPUTES faithfully (the `Eq.refl` compute-oracle proves the
/// recursor iota-reduces to `succ zero`), because a universe bump never touches
/// iota reduction.
#[test]
fn test_retry_flips_set_valued_recursor_and_computes_faithfully() {
    use clean_kernel::expr::BinderInfo;
    let mut env = Environment::try_with_prelude().expect("prelude env");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let one = Expr::app(succ.clone(), zero.clone());
    // Motive `λ _:Nat, Nat` — returns the type `Nat : Sort 1`.
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    // Faithful identity rebuild: succ case `λ (n:Nat) (ih:Nat), Nat.succ ih`.
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::app(succ.clone(), Expr::bvar(0)),
        ),
    );
    let make_value = |lvl: Level| {
        let rec = Expr::const_(Name::from_string("Nat.rec"), vec![lvl]);
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(rec, motive.clone()), zero.clone()),
                succ_case.clone(),
            ),
            one.clone(),
        )
    };
    let name = Name::from_string("test_set_elim_foo");
    // The speculative level-0 value is kernel-REJECTED (`Sort 1 ⋢ Sort 0`).
    let value0 = make_value(Level::zero());
    let decl0 = build_value_bearing_decl(&name, DeclKind::Definition, &[], &nat, &value0);
    assert!(
        env.add_decl(decl0).is_err(),
        "a Set-valued motive under `Nat.rec.{{0}}` must be kernel-rejected"
    );
    // The monotone retry bumps the recursor to `{1}` and the kernel accepts it.
    let verdict = retry_speculative_motive_universe(
        &mut env,
        &name,
        DeclKind::Definition,
        &[],
        &nat,
        &value0,
    );
    assert!(
        matches!(verdict, Some(AddConstResult::KernelVerified)),
        "the level-bump retry must flip the Set-valued elimination to \
         KernelVerified, got {verdict:?}"
    );
    // COMPUTE FIDELITY: the retry-accepted `foo` must iota-reduce to `succ zero`.
    // `Eq.refl Nat (succ zero) : Eq Nat (succ zero) (succ zero)` typechecks
    // against the declared `Eq Nat foo (succ zero)` ONLY if `foo ≡ succ zero` —
    // the kernel's def-eq is the compute oracle.
    let lvl1 = Level::succ(Level::zero());
    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
                nat.clone(),
            ),
            Expr::const_(name.clone(), vec![]),
        ),
        one.clone(),
    );
    let refl = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Eq.refl"), vec![lvl1.clone()]),
            nat.clone(),
        ),
        one.clone(),
    );
    let check = Declaration::Definition {
        name: Name::from_string("test_set_elim_check"),
        level_params: vec![],
        type_: eq_ty,
        value: refl,
        is_reducible: false,
    };
    assert!(
        env.add_decl(check).is_ok(),
        "the retry-accepted recursor value must COMPUTE to `succ zero` \
         (a universe bump cannot change iota reduction)"
    );
}

/// NEGATIVE CONTROL: the retry must NEVER launder an ill-typed recursor value
/// into a false `KernelVerified`. A branch with a genuine TYPE error (the type
/// `Nat : Sort 1` where a `Nat` *value* is required) is rejected at every
/// universe level — the retry exhausts its bumps and returns `None`, so the
/// constant falls through to the clean type-only axiom, exactly as before.
#[test]
fn test_retry_does_not_launder_ill_typed_recursor_value() {
    use clean_kernel::expr::BinderInfo;
    let mut env = Environment::try_with_prelude().expect("prelude env");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::app(succ.clone(), Expr::bvar(0)),
        ),
    );
    // CORRUPTED zero branch: `Nat` (the type, `: Sort 1`) where the zero minor
    // must be a `Nat` *value* — a structural type error no level bump rescues.
    let rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let bad_value = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), nat.clone()), succ_case),
        zero.clone(),
    );
    let name = Name::from_string("test_bad_set_elim");
    // The corrupted value DOES carry a bumpable recursor (the retry genuinely
    // tries), yet every bump still rejects the ill-typed branch.
    assert!(
        bump_recursor_motive_levels(&bad_value).is_some(),
        "the corrupted value still carries a recursor instance to retry"
    );
    let verdict = retry_speculative_motive_universe(
        &mut env,
        &name,
        DeclKind::Definition,
        &[],
        &nat,
        &bad_value,
    );
    assert!(
        verdict.is_none(),
        "a level bump must NOT launder an ill-typed recursor value into \
         KernelVerified, got {verdict:?}"
    );
}

/// End-to-end for the level-COUNT retry on a REAL Prop-only recursor. `Or.rec`
/// is Prop-only (`Or` has two constructors → not a subsingleton → eliminates
/// into `Prop` ONLY), so the kernel declares it with ZERO level params (no
/// motive universe). The Coq importer's Case lowering nonetheless emits it at
/// the speculative motive-universe arity `Or.rec.{0}` (one level), which the
/// kernel rejects on the strict level-count check
/// (`crates/clean-kernel/src/tc/infer.rs`). The retry realigns the arity to the
/// declared 0 and the kernel accepts it — this is the morphim/gproduct/imset2
/// `Level count mismatch … declared 0 … got 1` cluster in miniature.
#[test]
fn test_count_fix_flips_prop_only_recursor_to_kv() {
    let mut env = Environment::try_with_prelude().expect("prelude env");
    let rec_name = Name::from_string("Or.rec");
    let info = env
        .get_const(&rec_name)
        .expect("Or.rec is in the prelude")
        .clone();
    assert_eq!(
        info.level_params.len(),
        0,
        "Or.rec must be a Prop-only (zero-level) recursor for this fixture"
    );
    // A well-typed bare recursor reference emitted with ONE too many universe
    // levels: the ONLY defect is the level ARITY. The declared type is exactly
    // the recursor's own type, so nothing but the arity can reject it.
    let ty = info.type_.clone();
    let over_leveled = Expr::const_(rec_name.clone(), vec![Level::zero()]);
    let name = Name::from_string("test_count_fix_orrec");
    // The speculative value is kernel-REJECTED, specifically on LevelCountMismatch.
    let decl0 = build_value_bearing_decl(&name, DeclKind::Definition, &[], &ty, &over_leveled);
    let err = env
        .add_decl(decl0)
        .expect_err("an over-leveled Prop-only recursor reference must reject");
    assert!(
        err.to_string().contains("Level count mismatch"),
        "expected a LevelCountMismatch rejection, got: {err}"
    );
    // The count-fix retry realigns `Or.rec.{0}` -> `Or.rec` (zero levels) and
    // the kernel accepts it: KernelVerified.
    let verdict = retry_speculative_motive_universe(
        &mut env,
        &name,
        DeclKind::Definition,
        &[],
        &ty,
        &over_leveled,
    );
    assert!(
        matches!(verdict, Some(AddConstResult::KernelVerified)),
        "the level-COUNT fix must flip the Prop-only recursor reference to \
         KernelVerified, got {verdict:?}"
    );
    // The constant genuinely landed with the arity-corrected value.
    assert!(
        env.get_const(&name).is_some(),
        "the arity-corrected value must be installed under the name"
    );
}

/// NEGATIVE CONTROL for the level-COUNT retry: arity correction must NEVER
/// launder a value with a GENUINE type error into a false `KernelVerified`.
/// The value carries a count-mismatched recursor (so the count-fix truly fires),
/// but its declared type is one the recursor does NOT have — a real structural
/// mismatch that no arity/level adjustment can rescue. The retry exhausts both
/// the count fix and the bump ladder and returns `None`; nothing is installed.
#[test]
fn test_count_fix_does_not_launder_ill_typed_recursor_value() {
    let mut env = Environment::try_with_prelude().expect("prelude env");
    let rec_name = Name::from_string("Or.rec");
    // `Or.rec.{0}` — over-leveled (the arity defect the count-fix WOULD correct)...
    let over_leveled = Expr::const_(rec_name, vec![Level::zero()]);
    // ...but declared at a type `Or.rec` genuinely does NOT have (`Nat`): a real
    // structural mismatch, not a mere universe/arity slip.
    let wrong_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let name = Name::from_string("test_count_fix_illtyped");
    // Sanity: the count-fix genuinely FIRES on this value (there is a mismatched
    // recursor reference to correct) — the retry is really exercised, not a no-op.
    assert!(
        fix_recursor_level_counts(&env, &over_leveled).is_some(),
        "the value must carry a count-mismatched recursor for the retry to correct"
    );
    let verdict = retry_speculative_motive_universe(
        &mut env,
        &name,
        DeclKind::Definition,
        &[],
        &wrong_ty,
        &over_leveled,
    );
    assert!(
        verdict.is_none(),
        "arity correction must NOT launder a value whose declared type is wrong \
         into KernelVerified, got {verdict:?}"
    );
    assert!(
        env.get_const(&name).is_none(),
        "no constant may be installed for a rejected ill-typed value"
    );
}

/// ENV-DIRECTED PER-INSTANCE template-poly `prod` flip (round 3): each
/// `prod`/`pair`/`prod.rec` instance flips `{1,1}`→`{0,0}` (recursor
/// `{m,1,1}`→`{m,0,0}`, motive `m` preserved) ONLY where its two TYPE arguments
/// are provably `Prop`. A mixed term — a `Prop`-arg `prod P Q` next to a
/// `Type`-arg `prod R1 R2` — flips ONLY the `Prop` instance; the `Type` carrier
/// stays `{1,1}`. A term with no flippable instance returns `None`.
#[test]
fn test_flip_template_poly_prod_per_instance_flips_only_prop_args() {
    use clean_kernel::expr::{ExprKind, LevelVec};

    // Env: P, Q : Prop (flippable); R1, R2 : Type 1 (must stay {1,1}).
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let mut env = Environment::new();
    for (n, ty) in [("P", &prop), ("Q", &prop), ("R1", &type1), ("R2", &type1)] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(n),
            level_params: vec![],
            type_: ty.clone(),
        })
        .expect("axiom type is a well-formed sort");
    }

    let one = Level::succ(Level::zero());
    let mk_const = |name: &str, levels: &[Level]| {
        let mut lv = LevelVec::new();
        for l in levels {
            lv.push(l.clone());
        }
        Expr::from_kind(ExprKind::Const(Name::from_string(name), lv))
    };
    let cst = |n: &str| Expr::const_(Name::from_string(n), vec![]);
    let prod = |a: Expr, b: Expr| {
        Expr::app(
            Expr::app(
                mk_const("Coq.Init.Datatypes.prod.0", &[one.clone(), one.clone()]),
                a,
            ),
            b,
        )
    };
    let head_levels = |e: &Expr| match e.get_app_fn().kind() {
        ExprKind::Const(_, ls) => ls.to_vec(),
        other => panic!("expected const head, got {other:?}"),
    };

    // MIXED: foo (prod P Q) (prod R1 R2) — the Prop instance flips, the Type
    // carrier stays {1,1}. `foo` need not exist; only the prod args are peeled.
    let prod_pq = prod(cst("P"), cst("Q"));
    let prod_rr = prod(cst("R1"), cst("R2"));
    let mixed = Expr::app(Expr::app(cst("foo"), prod_pq.clone()), prod_rr.clone());
    let flipped = super::flip_template_poly_prod_per_instance(&env, &mixed)
        .expect("the Prop prod instance flips");
    let args = flipped.get_app_args();
    assert_eq!(
        head_levels(args[0]),
        vec![Level::zero(), Level::zero()],
        "prod P Q (both args Prop) collapses to prod.{{0,0}}"
    );
    assert_eq!(
        head_levels(args[1]),
        vec![one.clone(), one.clone()],
        "prod R1 R2 (Type carriers) stays at prod.{{1,1}}"
    );

    // eqmx unlock in isolation: prod P Q -> prod.{0,0} P Q.
    let flipped_pq =
        super::flip_template_poly_prod_per_instance(&env, &prod_pq).expect("all-Prop prod flips");
    assert_eq!(head_levels(&flipped_pq), vec![Level::zero(), Level::zero()]);

    // recursor prod.0.rec.{m,1,1} P Q -> {m,0,0} (motive m=1 kept, poly flipped).
    let m = Level::succ(Level::zero());
    let rec = Expr::app(
        Expr::app(
            mk_const(
                "Coq.Init.Datatypes.prod.0.rec",
                &[m.clone(), one.clone(), one.clone()],
            ),
            cst("P"),
        ),
        cst("Q"),
    );
    let flipped_rec = super::flip_template_poly_prod_per_instance(&env, &rec)
        .expect("a Prop-arg recursor instance flips");
    assert_eq!(
        head_levels(&flipped_rec),
        vec![m.clone(), Level::zero(), Level::zero()],
        "the recursor motive slot is preserved; only the poly slots collapse"
    );

    // A Type-carrier prod alone does NOT flip: nothing to retry.
    assert!(
        super::flip_template_poly_prod_per_instance(&env, &prod_rr).is_none(),
        "prod R1 R2 (Type carriers) is left at {{1,1}} -> None"
    );

    // A term with no template-poly prod instance: nothing to retry.
    assert!(
        super::flip_template_poly_prod_per_instance(&env, &cst("P")).is_none(),
        "no prod instance -> None"
    );

    // is_provably_prop discriminates a Prop const from a Type carrier, and is
    // conservative on shapes it cannot peel (a bare `Prop`/`Type` sort is a
    // TYPE, never itself Prop-typed).
    assert!(super::is_provably_prop(&env, &cst("P")), "P : Prop");
    assert!(super::is_provably_prop(&env, &cst("Q")), "Q : Prop");
    assert!(!super::is_provably_prop(&env, &cst("R1")), "R1 : Type 1");
    assert!(
        !super::is_provably_prop(&env, &prop),
        "the sort `Prop` is a Type, not itself Prop-typed"
    );
}

/// ROUND-4 BINDER-SORT-AWARE flip (the `real_maxrN`/`leqif`-family shape): a
/// `prod` whose two type arguments are de Bruijn VARIABLES bound by an enclosing
/// `: Prop` binder (`fun (A B : Prop) => A * B`) is a prod-of-Props. The
/// concrete-arg flip leaves it at `{1,1}` (a bare `BVar` is not provably `Prop`
/// on its own); the binder-sort-aware `_deep` flip recognizes the `: Prop`
/// binders and flips to `{0,0}`. A `: Type 1` binder is the negative control —
/// the prod stays `{1,1}` even under the deep flip.
#[test]
fn test_flip_binder_sort_aware_flips_prop_bound_prod() {
    use clean_kernel::expr::{BinderInfo, ExprKind, LevelVec};

    let one = Level::succ(Level::zero());
    let mk_prod_over_bvars = |lvl: &Level| {
        let mut lv = LevelVec::new();
        lv.push(lvl.clone());
        lv.push(lvl.clone());
        let head = Expr::from_kind(ExprKind::Const(
            Name::from_string("Coq.Init.Datatypes.prod.0"),
            lv,
        ));
        // `prod (BVar 1) (BVar 0)` — under two binders, `A = BVar 1`, `B = BVar 0`.
        Expr::app(Expr::app(head, Expr::bvar(1)), Expr::bvar(0))
    };
    let wrap2 = |sort: Expr, inner: Expr| {
        Expr::lam(
            BinderInfo::Default,
            sort.clone(),
            Expr::lam(BinderInfo::Default, sort, inner),
        )
    };
    // Dig through the two lambdas to the innermost prod head's level instance.
    fn head_levels(e: &Expr) -> Vec<Level> {
        use clean_kernel::expr::ExprKind as K;
        match e.kind() {
            K::Lam(_, _, b) => head_levels(b),
            K::App(..) => match e.get_app_fn().kind() {
                K::Const(_, ls) => ls.to_vec(),
                other => panic!("expected const prod head, got {other:?}"),
            },
            other => panic!("expected lam/app, got {other:?}"),
        }
    }

    let env = Environment::new();
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type1 = Expr::from_kind(ExprKind::Sort(one.clone()));

    // `fun (A B : Prop) => A * B` at {1,1}.
    let prop_body = wrap2(prop, mk_prod_over_bvars(&one));
    // Concrete-arg flip: bare `BVar` args are not provably Prop -> nothing to do.
    assert!(
        super::flip_template_poly_prod_per_instance(&env, &prop_body).is_none(),
        "concrete flip leaves a BVar-arg prod at {{1,1}}"
    );
    // Binder-sort-aware flip: the `: Prop` binders make A, B propositions -> {0,0}.
    let deep = super::flip_template_poly_prod_per_instance_deep(&env, &prop_body)
        .expect("binder-aware flip flips the Prop-bound prod");
    assert_eq!(
        head_levels(&deep),
        vec![Level::zero(), Level::zero()],
        "prod over `: Prop`-bound variables collapses to prod.{{0,0}}"
    );

    // NEGATIVE CONTROL: `fun (A B : Type 1) => A * B` — the deep flip must NOT
    // touch a prod over `: Type 1`-bound variables (they are not propositions).
    let type_body = wrap2(type1, mk_prod_over_bvars(&one));
    assert!(
        super::flip_template_poly_prod_per_instance_deep(&env, &type_body).is_none(),
        "NEGATIVE CONTROL: prod over `: Type 1`-bound variables stays {{1,1}}"
    );
}

/// The generalized motive-universe bump (Brick 1): it bumps ONLY level slot 0
/// (the motive) of a template-poly recursor instance `[motive, u, v]`, leaving
/// the inductive's own universe params (`u`, `v`) untouched.
#[test]
fn test_bump_recursor_motive_levels_bumps_only_slot_zero_on_poly_recursor() {
    use clean_kernel::expr::{ExprKind, LevelVec};

    let one = Level::succ(Level::zero());
    let mut lv = LevelVec::new();
    lv.push(Level::zero()); // motive
    lv.push(one.clone()); // u
    lv.push(one.clone()); // v
    let rec = Expr::from_kind(ExprKind::Const(
        Name::from_string("Coq.Init.Datatypes.prod.0.rec"),
        lv,
    ));
    let bumped = bump_recursor_motive_levels(&rec).expect("slot 0 is a concrete numeral to bump");
    match bumped.kind() {
        ExprKind::Const(_, ls) => assert_eq!(
            ls.to_vec(),
            vec![Level::succ(Level::zero()), one.clone(), one.clone()],
            "only the motive (slot 0) is bumped; the poly slots u,v are unchanged"
        ),
        other => panic!("expected const, got {other:?}"),
    }
}
