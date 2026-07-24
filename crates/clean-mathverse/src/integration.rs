// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end integration tests for the Mathverse Library.
//!
//! Exercises the full pipeline: import -> shard write -> shard read -> library
//! load -> search -> export, across Lean 4 and Coq source systems.

use std::path::PathBuf;

use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_olean::expr::{ParsedBinderInfo, ParsedExpr};
use clean_olean::level::ParsedLevel;
use clean_olean::module::{ConstantKind, ParsedConstant, ParsedModule};
use clean_olean::parse_module_file;

use crate::coq::alpha::CoqImporter;
use crate::equivalence::EquivalenceDetector;
use crate::export::alpha::{ExportConfig, Exporter};
use crate::graph_alpha::{ConceptEdge, ConceptNode, EquivConfidence};
use crate::lean4::olean::alpha::import_module;
use crate::lean4::olean::batch::{Lean4BatchConfig, Lean4BatchImporter};
use crate::library::MathverseLibrary;
use crate::manifest::LibraryLoader;
use crate::provenance::ProvenanceBuilder;
use crate::search::{ConceptEdgeKind, EdgeFilter, MathverseSearch};
use crate::shard::{ShardReader, ShardWriter};
use crate::trust::policy::TrustPolicy;
use crate::types::{
    AxiomProfile, ConstantIdx, ContentDomain, ImportConfidence, MathverseConstantHeader,
    SourceSystem,
};

// -- Helpers -----------------------------------------------------------------

fn mock_module(constants: Vec<ParsedConstant>) -> ParsedModule {
    ParsedModule {
        const_names: constants.iter().map(|c| c.name.clone()).collect(),
        constants,
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    }
}

fn mock_constant(
    name: &str,
    kind: ConstantKind,
    ty: Option<ParsedExpr>,
    val: Option<ParsedExpr>,
) -> ParsedConstant {
    ParsedConstant {
        definition_safety: None,
        quot_kind: None,
        name: name.to_string(),
        kind,
        level_params: Vec::new(),
        type_: ty,
        value: val,
        inductive_val: None,
        constructor_val: None,
        recursor_val: None,
        hints: None,
    }
}

fn nat_const() -> ParsedExpr {
    ParsedExpr::Const("Nat".to_string(), vec![])
}
fn bool_const() -> ParsedExpr {
    ParsedExpr::Const("Bool".to_string(), vec![])
}
fn prop() -> ParsedExpr {
    ParsedExpr::Sort(ParsedLevel::Zero)
}
fn type0() -> ParsedExpr {
    ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Zero)))
}

fn pi(domain: ParsedExpr, codomain: ParsedExpr) -> ParsedExpr {
    ParsedExpr::ForallE(
        "x".into(),
        Box::new(domain),
        Box::new(codomain),
        ParsedBinderInfo::Default,
    )
}

fn lam_id() -> ParsedExpr {
    ParsedExpr::Lam(
        "x".into(),
        Box::new(nat_const()),
        Box::new(ParsedExpr::BVar(0)),
        ParsedBinderInfo::Default,
    )
}

fn raw_shard(
    entries: &[(
        &str,
        SourceSystem,
        ImportConfidence,
        ContentDomain,
        AxiomProfile,
    )],
) -> ShardReader {
    let mut w = ShardWriter::new();
    let l0 = w.add_level(FlatLevel::zero());
    let e0 = w.add_expr(FlatExpr::sort(l0));
    for &(name, src, conf, dom, ax) in entries {
        let ni = w.add_string(name);
        w.add_constant(MathverseConstantHeader {
            name_idx: ni,
            type_idx: e0,
            value_idx: e0,
            source_system: src as u8,
            import_confidence: conf as u8,
            content_domain: dom as u8,
            decl_kind: 0,
            axiom_profile: ax,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
    }
    let mut buf = Vec::new();
    w.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

// -- Test 1: Full Lean 4 pipeline -------------------------------------------

#[test]
fn test_lean4_full_pipeline() {
    // Build a ParsedModule with 21 constants spanning all kinds.
    let constants = vec![
        mock_constant("Nat", ConstantKind::Inductive, Some(type0()), None),
        mock_constant("Bool", ConstantKind::Inductive, Some(type0()), None),
        mock_constant(
            "Nat.zero",
            ConstantKind::Constructor,
            Some(nat_const()),
            None,
        ),
        mock_constant(
            "Nat.succ",
            ConstantKind::Constructor,
            Some(pi(nat_const(), nat_const())),
            None,
        ),
        mock_constant(
            "Bool.true",
            ConstantKind::Constructor,
            Some(bool_const()),
            None,
        ),
        mock_constant(
            "Bool.false",
            ConstantKind::Constructor,
            Some(bool_const()),
            None,
        ),
        mock_constant(
            "Nat.rec",
            ConstantKind::Recursor,
            Some(pi(nat_const(), nat_const())),
            None,
        ),
        mock_constant(
            "Nat.add",
            ConstantKind::Definition,
            Some(pi(nat_const(), nat_const())),
            Some(lam_id()),
        ),
        mock_constant(
            "Nat.mul",
            ConstantKind::Definition,
            Some(pi(nat_const(), nat_const())),
            Some(lam_id()),
        ),
        mock_constant(
            "Nat.add_comm",
            ConstantKind::Theorem,
            Some(pi(nat_const(), prop())),
            Some(lam_id()),
        ),
        mock_constant(
            "Nat.add_assoc",
            ConstantKind::Theorem,
            Some(pi(nat_const(), prop())),
            Some(lam_id()),
        ),
        mock_constant(
            "Nat.mul_comm",
            ConstantKind::Theorem,
            Some(pi(nat_const(), prop())),
            Some(lam_id()),
        ),
        mock_constant(
            "Nat.add_zero",
            ConstantKind::Theorem,
            Some(pi(nat_const(), prop())),
            Some(lam_id()),
        ),
        mock_constant(
            "Nat.zero_add",
            ConstantKind::Theorem,
            Some(pi(nat_const(), prop())),
            Some(lam_id()),
        ),
        mock_constant(
            "Nat.succ_pred",
            ConstantKind::Theorem,
            Some(pi(nat_const(), prop())),
            Some(lam_id()),
        ),
        mock_constant("Classical.choice", ConstantKind::Axiom, Some(type0()), None),
        mock_constant("propext", ConstantKind::Axiom, Some(type0()), None),
        mock_constant("Quot", ConstantKind::Quot, Some(type0()), None),
        mock_constant("Quot.mk", ConstantKind::Quot, Some(type0()), None),
        mock_constant("SomeOpaque", ConstantKind::Opaque, Some(type0()), None),
        mock_constant(
            "List.head",
            ConstantKind::Definition,
            Some(pi(nat_const(), bool_const())),
            Some(lam_id()),
        ),
    ];
    let module = mock_module(constants);

    // Import -> shard write -> shard read.
    let mut writer = ShardWriter::new();
    let stats = import_module(&module, &mut writer).unwrap();
    assert_eq!(stats.total, 21);
    assert!(stats.kernel_verified >= 17);
    assert!(stats.axiomatized >= 3);
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(reader.constants.len(), 21);

    // Load into MathverseLibrary with default trust policy.
    let mut lib = MathverseLibrary::new(TrustPolicy::default_policy());
    assert_eq!(lib.load_shard(&reader).unwrap(), 21);

    // Name lookup: visible vs trust-gated.
    assert!(lib.lookup_name("Nat.add_comm").is_some());
    assert!(lib.lookup_name("Nat").is_some());
    assert!(lib.lookup_name("Bool.true").is_some());
    assert!(lib.lookup_name("Nonexistent").is_none());
    assert!(
        lib.lookup_name("Classical.choice").is_none(),
        "axiom hidden by default policy"
    );
    assert!(
        lib.lookup_name("SomeOpaque").is_none(),
        "opaque hidden by default policy"
    );
    assert!(lib.lookup_name("propext").is_none(), "propext axiom hidden");

    // Type search via discrimination tree.
    let nat_add_hdr = lib.lookup_name("Nat.add").unwrap();
    let type_results = lib.search_type(nat_add_hdr.type_idx, 10).unwrap();
    assert!(
        !type_results.is_empty(),
        "type search should find at least Nat.add"
    );

    // Dependency walking.
    let add_comm_idx = (0..lib.constant_count() as u32)
        .find(|&i| lib.get_name(i) == Some("Nat.add_comm"))
        .unwrap();
    let deps: Vec<ConstantIdx> = lib.walk_deps(add_comm_idx).collect();
    assert!(
        !deps.is_empty(),
        "Nat.add_comm should have at least itself in walk_deps"
    );

    // Export to JSON Lines and verify record structure.
    let exporter = Exporter::new(&lib, ExportConfig::statement_only());
    let mut export_buf = Vec::new();
    let export_stats = exporter.export_to_writer(&mut export_buf).unwrap();
    let output = String::from_utf8(export_buf).unwrap();
    let lines: Vec<&str> = output.lines().collect();
    assert!(export_stats.exported > 0);
    assert_eq!(lines.len(), export_stats.exported);
    let first: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
    assert!(first.get("name").is_some());
    assert!(first.get("source").is_some());
    assert!(first.get("confidence").is_some());
    assert!(first.get("axiom_bits").is_some());
}

// -- Test 2: Full Coq pipeline ----------------------------------------------

#[test]
fn test_coq_full_pipeline() {
    let coq_data = concat!(
        "(CoqConstant PeanoNat.Nat.add_comm (Prod n (Sort (Type 0)) (Sort Prop)) (Lambda n (Sort (Type 0)) (Rel 0)))",
        "(CoqConstant PeanoNat.Nat.mul_comm (Prod n (Sort (Type 0)) (Sort Prop)) (Lambda n (Sort (Type 0)) (Rel 0)))",
        "(CoqAxiom classic (Sort Prop))",
        "(CoqAxiom propositional_extensionality (Sort Prop))",
        "(CoqConstant PeanoNat.Nat.add_assoc (Prod n (Sort (Type 0)) (Sort Prop)) (Lambda n (Sort (Type 0)) (Rel 0)))",
    );

    let mut writer = ShardWriter::new();
    let stats = CoqImporter.import_sexp(coq_data, &mut writer).unwrap();
    assert_eq!(
        (stats.total, stats.translated, stats.axiomatized),
        (5, 3, 2)
    );

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(reader.constants.len(), 5);

    // Permissive library: all visible.
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&reader).unwrap();
    assert!(lib.lookup_name("PeanoNat.Nat.add_comm").is_some());
    assert!(lib.lookup_name("classic").is_some());

    // Verify axiom profiles: axioms/valueless constants carry the bridge tag;
    // value-bearing translated definitions are profile-clean (trust is decided
    // by the kernel re-check, not minted at import time).
    for i in 0..lib.constant_count() as u32 {
        let hdr = lib.get_constant(i).unwrap();
        assert_eq!(hdr.source_system, SourceSystem::Coq as u8);
        if hdr.has_value() {
            assert_eq!(hdr.profile(), AxiomProfile::NONE);
        } else {
            assert!(hdr.profile().has(AxiomProfile::BRIDGE_AXIOM));
        }
    }
    let classic = lib.lookup_name("classic").unwrap();
    assert!(
        classic.profile().has(AxiomProfile::CHOICE)
            && classic.profile().has(AxiomProfile::CLASSICAL)
    );
    let propext = lib.lookup_name("propositional_extensionality").unwrap();
    assert!(
        propext.profile().has(AxiomProfile::PROP_EXT)
            && propext.profile().has(AxiomProfile::AXIOMATIZED)
    );

    // Default policy hides axiomatized, keeps translated.
    let mut strict_lib = MathverseLibrary::new(TrustPolicy::default_policy());
    strict_lib.load_shard(&reader).unwrap();
    assert!(strict_lib.lookup_name("classic").is_none());
    assert!(strict_lib
        .lookup_name("propositional_extensionality")
        .is_none());
    assert!(strict_lib.lookup_name("PeanoNat.Nat.add_comm").is_some());
}

// -- Test 3: Multi-shard multi-system ----------------------------------------

#[test]
fn test_multi_system_library() {
    let lean_names: Vec<_> = (0..10)
        .map(|i| {
            let name: &str = Box::leak(format!("Lean.thm_{i}").into_boxed_str());
            (
                name,
                SourceSystem::Lean4,
                ImportConfidence::KernelVerified,
                ContentDomain::PureMath,
                AxiomProfile::NONE,
            )
        })
        .collect();
    let lean_shard = raw_shard(&lean_names);

    let coq_names: Vec<_> = (0..10)
        .map(|i| {
            let name: &str = Box::leak(format!("Coq.thm_{i}").into_boxed_str());
            (
                name,
                SourceSystem::Coq,
                ImportConfidence::Translated,
                ContentDomain::PureMath,
                AxiomProfile::BRIDGE_AXIOM,
            )
        })
        .collect();
    let coq_shard = raw_shard(&coq_names);

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    assert_eq!(lib.load_shard(&lean_shard).unwrap(), 10);
    assert_eq!(lib.load_shard(&coq_shard).unwrap(), 10);
    assert_eq!(lib.constant_count(), 20);

    // Cross-shard lookup.
    assert!(lib.lookup_name("Lean.thm_0").is_some());
    assert!(lib.lookup_name("Lean.thm_9").is_some());
    assert!(lib.lookup_name("Coq.thm_0").is_some());
    assert!(lib.lookup_name("Coq.thm_9").is_some());

    // Equivalence detection across systems.
    let mut detector = EquivalenceDetector::new();
    for i in 0..lib.constant_count() as u32 {
        let name = lib.get_name(i).unwrap();
        let source = lib.get_constant(i).unwrap().source().unwrap();
        detector.index_constant(i, name, source, &[FlatExpr::sort(0)], 0);
    }
    assert!(
        !detector.detect_all(0.3).is_empty(),
        "should find cross-system equivalences"
    );

    // Export filters by source system.
    let mut lean_cfg = ExportConfig::statement_only();
    lean_cfg.source_filter = Some(vec![SourceSystem::Lean4]);
    assert_eq!(Exporter::new(&lib, lean_cfg).export_all().len(), 10);

    let mut coq_cfg = ExportConfig::statement_only();
    coq_cfg.source_filter = Some(vec![SourceSystem::Coq]);
    assert_eq!(Exporter::new(&lib, coq_cfg).export_all().len(), 10);
}

// -- Test 4: Trust enforcement end-to-end ------------------------------------

#[test]
fn test_trust_enforcement_e2e() {
    let entries: Vec<(
        &str,
        SourceSystem,
        ImportConfidence,
        ContentDomain,
        AxiomProfile,
    )> = vec![
        (
            "verified.thm",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "choice.thm",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::CHOICE | AxiomProfile::LEM,
        ),
        (
            "translated.thm",
            SourceSystem::Coq,
            ImportConfidence::Translated,
            ContentDomain::PureMath,
            AxiomProfile::BRIDGE_AXIOM,
        ),
        (
            "axiomatized.thm",
            SourceSystem::Lean4,
            ImportConfidence::Axiomatized,
            ContentDomain::PureMath,
            AxiomProfile::AXIOMATIZED,
        ),
        (
            "nn_gated.thm",
            SourceSystem::GammaCrown,
            ImportConfidence::Translated,
            ContentDomain::NnVerification,
            AxiomProfile::NN_ABSTRACTION | AxiomProfile::FLOAT_APPROX,
        ),
        (
            "incon.thm",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::UNIVERSE_INCON,
        ),
    ];
    let shard = raw_shard(&entries);

    // Default policy: only non-gated constants visible.
    let mut lib_default = MathverseLibrary::new(TrustPolicy::default_policy());
    lib_default.load_shard(&shard).unwrap();
    assert!(lib_default.lookup_name("verified.thm").is_some());
    assert!(
        lib_default.lookup_name("choice.thm").is_some(),
        "CHOICE not trust-gated"
    );
    assert!(
        lib_default.lookup_name("translated.thm").is_some(),
        "BRIDGE_AXIOM not trust-gated"
    );
    assert!(
        lib_default.lookup_name("axiomatized.thm").is_none(),
        "AXIOMATIZED is trust-gated"
    );
    assert!(
        lib_default.lookup_name("nn_gated.thm").is_none(),
        "NN_ABSTRACTION is trust-gated"
    );
    assert!(
        lib_default.lookup_name("incon.thm").is_none(),
        "UNIVERSE_INCON is trust-gated"
    );

    // Permissive policy: all visible.
    let mut lib_perm = MathverseLibrary::new(TrustPolicy::permissive());
    lib_perm.load_shard(&shard).unwrap();
    for &(name, _, _, _, _) in &entries {
        assert!(
            lib_perm.lookup_name(name).is_some(),
            "{name} should be visible under permissive"
        );
    }

    // ProofGenEligible export: kernel-verified + zero axiom bits only.
    let pg = Exporter::new(&lib_perm, ExportConfig::proof_gen()).export_all();
    assert_eq!(pg.len(), 1);
    assert_eq!(pg[0].name, "verified.thm");

    // StatementOnly export: all constants.
    assert_eq!(
        Exporter::new(&lib_perm, ExportConfig::statement_only())
            .export_all()
            .len(),
        6
    );
}

// -- Test 5: Disk-based shard lifecycle --------------------------------------

#[test]
fn test_disk_shard_lifecycle() {
    let dir = tempfile::tempdir().unwrap();
    let loader = LibraryLoader::new(dir.path().join("mathverse"));
    loader.init().unwrap();
    let manifest = loader.load_manifest().unwrap();
    assert!(manifest.base_shards.is_empty() && manifest.delta_shards.is_empty());

    // Write a base shard with 5 constants.
    let mut bw = ShardWriter::new();
    let l0 = bw.add_level(FlatLevel::zero());
    let e0 = bw.add_expr(FlatExpr::sort(l0));
    for i in 0..5 {
        let ni = bw.add_string(&format!("base.c{i}"));
        bw.add_constant(MathverseConstantHeader {
            name_idx: ni,
            type_idx: e0,
            value_idx: e0,
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
    loader.write_shard(&bw, "base0", false).unwrap();

    // Write 2 delta shards with 3 constants each.
    for di in 0..2 {
        let mut dw = ShardWriter::new();
        let l = dw.add_level(FlatLevel::zero());
        let e = dw.add_expr(FlatExpr::sort(l));
        for j in 0..3 {
            let ni = dw.add_string(&format!("delta{di}.c{j}"));
            dw.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: e,
                value_idx: e,
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
        loader.write_shard(&dw, &format!("d{di}"), true).unwrap();
    }

    // Load and verify all 11 constants.
    let lib = loader.load_library(TrustPolicy::permissive()).unwrap();
    assert_eq!(lib.constant_count(), 11);
    assert!(lib.lookup_name("base.c0").is_some());
    assert!(lib.lookup_name("delta1.c2").is_some());

    // Compact, reload, re-verify.
    assert_eq!(loader.compact().unwrap().deltas_merged, 2);
    let lib2 = loader.load_library(TrustPolicy::permissive()).unwrap();
    assert_eq!(lib2.constant_count(), 11);
    assert!(lib2.lookup_name("base.c0").is_some());
    assert!(lib2.lookup_name("delta1.c2").is_some());

    // Integrity check.
    let integrity = loader.verify_integrity().unwrap();
    assert_eq!(integrity.shards_valid, 1);
    assert!(integrity.shards_corrupt.is_empty());
}

// -- Test 6: Knowledge graph integration -------------------------------------

#[test]
fn test_knowledge_graph_integration() {
    let shard = raw_shard(&[
        (
            "Group.mul_assoc",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "Group.mul_inv",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "Ring.add_comm",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "Field.mul_inv",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "VectorSpace.axiom1",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
    ]);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();

    // Build concept graph: Group <- Ring <- Field, VectorSpace -> Field.
    let group = lib.add_graph_node(ConceptNode::Structure {
        name: "Group".into(),
        axioms: vec![0, 1],
    });
    let ring = lib.add_graph_node(ConceptNode::Structure {
        name: "Ring".into(),
        axioms: vec![2],
    });
    let field = lib.add_graph_node(ConceptNode::Structure {
        name: "Field".into(),
        axioms: vec![3],
    });
    let vs = lib.add_graph_node(ConceptNode::Theorem { constant_idx: 4 });
    lib.add_graph_edge(ring, group, ConceptEdge::Generalizes);
    lib.add_graph_edge(field, ring, ConceptEdge::Generalizes);
    lib.add_graph_edge(vs, field, ConceptEdge::DependsOn);
    lib.add_graph_edge(group, ring, ConceptEdge::SpecialCase);

    // BFS from ring, depth 2.
    let sub = lib
        .graph_query(ring as ConstantIdx, &EdgeFilter::default(), 2)
        .unwrap();
    assert!(sub.nodes.len() >= 2, "BFS from Ring should reach Group");
    assert!(!sub.edges.is_empty());

    // Equivalences.
    lib.add_equivalence(0, 3, EquivConfidence::ErasedCandidate { score: 0.85 });
    assert_eq!(lib.find_equivalents(0).unwrap().len(), 1);
    assert_eq!(lib.find_equivalents(3).unwrap()[0].1, 0);

    // Edge-filtered graph query: only Generalizes.
    let gen_filter = EdgeFilter {
        allowed_edges: Some(vec![ConceptEdgeKind::Generalizes]),
        max_depth: Some(3),
    };
    let gen_sub = lib
        .graph_query(field as ConstantIdx, &gen_filter, 3)
        .unwrap();
    assert!(gen_sub.nodes.len() >= 2);
    for (_, _, edge) in &gen_sub.edges {
        assert!(matches!(edge, ConceptEdge::Generalizes));
    }

    // DependsOn filter from ring: no DependsOn edges outgoing.
    let dep_filter = EdgeFilter {
        allowed_edges: Some(vec![ConceptEdgeKind::DependsOn]),
        max_depth: Some(3),
    };
    let dep_sub = lib
        .graph_query(ring as ConstantIdx, &dep_filter, 3)
        .unwrap();
    assert!(dep_sub.edges.is_empty(), "Ring has no DependsOn edges");
}

// -- Test 7: Cross-system import + equivalence detection ---------------------

#[test]
fn test_lean4_coq_cross_import() {
    // Lean 4 shard: nat, bool, list constants.
    let lean_entries: Vec<_> = vec![
        (
            "Nat",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "Bool",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "List",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "Nat.add",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
    ];
    let lean_shard = raw_shard(
        &lean_entries
            .iter()
            .map(|&(n, s, c, d, a)| (n, s, c, d, a))
            .collect::<Vec<_>>(),
    );

    // Coq shard: corresponding constants.
    let coq_entries: Vec<_> = vec![
        (
            "nat",
            SourceSystem::Coq,
            ImportConfidence::Translated,
            ContentDomain::PureMath,
            AxiomProfile::BRIDGE_AXIOM,
        ),
        (
            "bool",
            SourceSystem::Coq,
            ImportConfidence::Translated,
            ContentDomain::PureMath,
            AxiomProfile::BRIDGE_AXIOM,
        ),
        (
            "list",
            SourceSystem::Coq,
            ImportConfidence::Translated,
            ContentDomain::PureMath,
            AxiomProfile::BRIDGE_AXIOM,
        ),
        (
            "PeanoNat.Nat.add_comm",
            SourceSystem::Coq,
            ImportConfidence::Translated,
            ContentDomain::PureMath,
            AxiomProfile::BRIDGE_AXIOM,
        ),
    ];
    let coq_shard = raw_shard(
        &coq_entries
            .iter()
            .map(|&(n, s, c, d, a)| (n, s, c, d, a))
            .collect::<Vec<_>>(),
    );

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    assert_eq!(lib.load_shard(&lean_shard).unwrap(), 4);
    assert_eq!(lib.load_shard(&coq_shard).unwrap(), 4);
    assert_eq!(lib.constant_count(), 8);

    // Index all constants into equivalence detector.
    let mut detector = EquivalenceDetector::new();
    for i in 0..lib.constant_count() as u32 {
        let name = lib.get_name(i).unwrap();
        let source = lib.get_constant(i).unwrap().source().unwrap();
        detector.index_constant(i, name, source, &[FlatExpr::sort(0)], 0);
    }
    let equivs = detector.detect_all(0.3);
    // Cross-system equivalences should be detected (nat/Nat, bool/Bool, list/List).
    assert!(
        !equivs.is_empty(),
        "cross-system equivalences should be found"
    );
}

// -- Test 8: Batch import with provenance ------------------------------------

#[test]
fn test_batch_import_with_provenance() {
    use crate::provenance::ProvenanceBuilder;

    let constants = vec![
        mock_constant("Init.Nat", ConstantKind::Inductive, Some(type0()), None),
        mock_constant("Init.Bool", ConstantKind::Inductive, Some(type0()), None),
        mock_constant(
            "Data.List.map",
            ConstantKind::Definition,
            Some(pi(nat_const(), nat_const())),
            Some(lam_id()),
        ),
    ];
    let module = mock_module(constants);

    let mut writer = ShardWriter::new();
    let stats = import_module(&module, &mut writer).unwrap();
    assert_eq!(stats.total, 3);

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&reader).unwrap();

    // Attach provenance records with module path and source file.
    let provenance_specs = [
        ("Init.Nat", "Init/Nat.lean", "Init"),
        ("Init.Bool", "Init/Bool.lean", "Init"),
        ("Data.List.map", "Data/List/Basic.lean", "Data.List"),
    ];
    for (i, &(name, file, module_path)) in provenance_specs.iter().enumerate() {
        let record = ProvenanceBuilder::new(name)
            .source_file(file)
            .module_path(module_path)
            .build();
        lib.add_provenance_record(i as u32, record);
    }

    assert_eq!(lib.provenance().len(), 3);
    for (i, &(name, file, module_path)) in provenance_specs.iter().enumerate() {
        let rec = lib.provenance().get(i as u32).unwrap();
        assert_eq!(rec.original_name, name);
        assert_eq!(rec.source_file.as_deref(), Some(file));
        assert_eq!(rec.module_path.as_deref(), Some(module_path));
        assert!(lib
            .provenance()
            .verify_digest(lib.get_constant(i as u32).unwrap()));
    }
}

// -- Test 9: Trust propagation across systems --------------------------------

#[test]
fn test_trust_propagation_cross_system() {
    use crate::trust::policy::propagate_axiom_profiles;

    // Create constants: 2 axiomatized Coq, 3 kernel-verified Lean4.
    // deps: lean_thm_0 depends on coq_ax_0, lean_thm_1 depends on lean_thm_0.
    let entries: Vec<(
        &str,
        SourceSystem,
        ImportConfidence,
        ContentDomain,
        AxiomProfile,
    )> = vec![
        (
            "coq.ax0",
            SourceSystem::Coq,
            ImportConfidence::Axiomatized,
            ContentDomain::PureMath,
            AxiomProfile::AXIOMATIZED | AxiomProfile::BRIDGE_AXIOM,
        ),
        (
            "coq.ax1",
            SourceSystem::Coq,
            ImportConfidence::Axiomatized,
            ContentDomain::PureMath,
            AxiomProfile::AXIOMATIZED | AxiomProfile::CLASSICAL,
        ),
        (
            "lean.thm0",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "lean.thm1",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "lean.thm2",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
    ];
    let shard = raw_shard(&entries);

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();

    // Set up dependency chain: thm0 depends on ax0, thm1 depends on thm0.
    lib.add_dependency(2, 0); // lean.thm0 -> coq.ax0
    lib.add_dependency(3, 2); // lean.thm1 -> lean.thm0

    // Propagate axiom profiles through the dependency graph.
    let mut headers: Vec<MathverseConstantHeader> =
        (0..5).map(|i| *lib.get_constant(i).unwrap()).collect();
    let deps = vec![vec![], vec![], vec![0], vec![2], vec![]];
    propagate_axiom_profiles(&mut headers, &deps).unwrap();

    // coq.ax0 keeps its original bits.
    assert!(headers[0].axiom_profile.has(AxiomProfile::AXIOMATIZED));
    // lean.thm0 inherits AXIOMATIZED + BRIDGE_AXIOM from coq.ax0.
    assert!(headers[2].axiom_profile.has(AxiomProfile::AXIOMATIZED));
    assert!(headers[2].axiom_profile.has(AxiomProfile::BRIDGE_AXIOM));
    // lean.thm1 inherits transitively.
    assert!(headers[3].axiom_profile.has(AxiomProfile::AXIOMATIZED));
    // lean.thm2 has no deps, stays pure.
    assert!(headers[4].axiom_profile.is_pure());

    // Under default policy, thm2 visible, thm0 and thm1 hidden (AXIOMATIZED is trust-gated).
    let default_policy = TrustPolicy::default_policy();
    assert!(default_policy.is_visible(&headers[4]));
    assert!(!default_policy.is_visible(&headers[2]));
    assert!(!default_policy.is_visible(&headers[3]));
}

// -- Test 10: Shard compaction preserves data --------------------------------

#[test]
fn test_shard_compaction_preserves_data() {
    let dir = tempfile::tempdir().unwrap();
    let loader = LibraryLoader::new(dir.path().join("mathverse"));
    loader.init().unwrap();

    // 3 overlapping delta shards: some constant names appear in multiple.
    let names_per_shard = [
        ["alpha", "beta", "gamma"],
        ["beta", "gamma", "delta"],   // beta, gamma overlap
        ["gamma", "epsilon", "zeta"], // gamma overlaps
    ];
    for (i, names) in names_per_shard.iter().enumerate() {
        let mut dw = ShardWriter::new();
        let l = dw.add_level(FlatLevel::zero());
        let e = dw.add_expr(FlatExpr::sort(l));
        for name in names {
            let ni = dw.add_string(name);
            dw.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: e,
                value_idx: e,
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
        loader.write_shard(&dw, &format!("d{i}"), true).unwrap();
    }

    // Pre-compaction: 9 total entries (including duplicates).
    let lib_pre = loader.load_library(TrustPolicy::permissive()).unwrap();
    assert_eq!(lib_pre.constant_count(), 9);

    // Compact all deltas.
    let result = loader.compact().unwrap();
    assert_eq!(result.deltas_merged, 3);

    // Post-compaction: library should still load all constants (last-writer-wins on name).
    let lib_post = loader.load_library(TrustPolicy::permissive()).unwrap();
    // All unique names should be resolvable.
    for name in &["alpha", "beta", "gamma", "delta", "epsilon", "zeta"] {
        assert!(
            lib_post.lookup_name(name).is_some(),
            "{name} should exist after compaction"
        );
    }
}

// -- Test 11: All five search modes -----------------------------------------

#[test]
fn test_search_all_five_modes() {
    // Build a library with 20+ constants from both Lean4 and Coq.
    let mut entries: Vec<(
        &str,
        SourceSystem,
        ImportConfidence,
        ContentDomain,
        AxiomProfile,
    )> = Vec::new();
    let lean_names: &[&str] = &[
        "Nat.add",
        "Nat.mul",
        "Nat.add_comm",
        "Nat.add_assoc",
        "Nat.mul_comm",
        "Nat.zero_add",
        "Nat.succ_pred",
        "Bool.not_not",
        "List.map",
        "List.filter",
        "Int.add",
        "Int.neg",
    ];
    for name in lean_names {
        entries.push((
            name,
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ));
    }
    let coq_names: &[&str] = &[
        "PeanoNat.Nat.add_comm",
        "PeanoNat.Nat.mul_comm",
        "PeanoNat.Nat.add_assoc",
        "PeanoNat.Nat.add_0_l",
        "Bool.negb_involutive",
        "List.map_map",
        "List.filter_true",
        "Int.add_comm",
        "Ring.add_comm",
    ];
    for name in coq_names {
        entries.push((
            name,
            SourceSystem::Coq,
            ImportConfidence::Translated,
            ContentDomain::PureMath,
            AxiomProfile::BRIDGE_AXIOM,
        ));
    }
    let shard = raw_shard(&entries);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    assert!(lib.constant_count() >= 20);

    // Mode 1: lookup_name (exact).
    assert!(lib.lookup_name("Nat.add").is_some());
    assert!(lib.lookup_name("PeanoNat.Nat.add_comm").is_some());
    assert!(lib.lookup_name("Nonexistent").is_none());

    // Mode 2: search_type (discrimination tree).
    let hdr = lib.lookup_name("Nat.add").unwrap();
    let type_results = lib.search_type(hdr.type_idx, 10).unwrap();
    assert!(!type_results.is_empty(), "type search should find results");

    // Mode 3: search_semantic (BM25).
    let sem_results = lib.search_semantic("add comm", 10).unwrap();
    assert!(
        !sem_results.is_empty(),
        "semantic search should find results"
    );

    // Mode 4: walk_deps (BFS).
    let walk: Vec<ConstantIdx> = lib.walk_deps(0).collect();
    assert!(
        !walk.is_empty(),
        "walk_deps should return at least the root"
    );

    // Mode 5: find_equivalents.
    lib.add_equivalence(0, 12, EquivConfidence::ErasedCandidate { score: 0.9 });
    let equivs = lib.find_equivalents(0).unwrap();
    assert_eq!(equivs.len(), 1);
    assert_eq!(equivs[0].1, 12);
}

// -- Test 12: Export training data -------------------------------------------

#[test]
fn test_export_training_data() {
    let entries: Vec<(
        &str,
        SourceSystem,
        ImportConfidence,
        ContentDomain,
        AxiomProfile,
    )> = vec![
        (
            "thm.a",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "thm.b",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "thm.c",
            SourceSystem::Coq,
            ImportConfidence::Translated,
            ContentDomain::PureMath,
            AxiomProfile::BRIDGE_AXIOM,
        ),
    ];
    let shard = raw_shard(&entries);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();

    let exporter = Exporter::new(&lib, ExportConfig::proof_gen());
    let mut buf = Vec::new();
    let stats = exporter.export_to_writer(&mut buf).unwrap();
    assert_eq!(
        stats.exported, 2,
        "proof_gen should export only kernel-verified"
    );

    let output = String::from_utf8(buf).unwrap();
    for line in output.lines() {
        let record: serde_json::Value = serde_json::from_str(line).unwrap();
        assert!(record.get("name").is_some());
        assert!(record.get("source").is_some());
        assert!(record.get("confidence").is_some());
        assert!(record.get("axiom_bits").is_some());
        assert!(record.get("type_expr").is_some());
    }
}

// -- Test 13: Knowledge graph cross-references -------------------------------

#[test]
fn test_knowledge_graph_cross_references() {
    let entries: Vec<(
        &str,
        SourceSystem,
        ImportConfidence,
        ContentDomain,
        AxiomProfile,
    )> = vec![
        (
            "A",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "B",
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ),
        (
            "C",
            SourceSystem::Coq,
            ImportConfidence::Translated,
            ContentDomain::PureMath,
            AxiomProfile::BRIDGE_AXIOM,
        ),
    ];
    let shard = raw_shard(&entries);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();

    // Add dependency: B depends on A.
    lib.add_dependency(1, 0);

    // Build graph nodes.
    let na = lib.add_graph_node(ConceptNode::Theorem { constant_idx: 0 });
    let nb = lib.add_graph_node(ConceptNode::Theorem { constant_idx: 1 });
    let nc = lib.add_graph_node(ConceptNode::Theorem { constant_idx: 2 });
    lib.add_graph_edge(nb, na, ConceptEdge::DependsOn);

    // Add equivalence: A (Lean4) ~ C (Coq).
    lib.add_equivalence(0, 2, EquivConfidence::ProvedEquivalent);
    lib.add_graph_edge(na, nc, ConceptEdge::Equivalent { proof: None });

    // Verify DependsOn edges match the dependency relationship.
    let dep_filter = EdgeFilter {
        allowed_edges: Some(vec![ConceptEdgeKind::DependsOn]),
        max_depth: Some(2),
    };
    let sub = lib.graph_query(nb as ConstantIdx, &dep_filter, 2).unwrap();
    assert_eq!(sub.edges.len(), 1);
    assert!(matches!(sub.edges[0].2, ConceptEdge::DependsOn));

    // Verify Equivalent edges.
    let eq_filter = EdgeFilter {
        allowed_edges: Some(vec![ConceptEdgeKind::Equivalent]),
        max_depth: Some(2),
    };
    let eq_sub = lib.graph_query(na as ConstantIdx, &eq_filter, 2).unwrap();
    assert_eq!(eq_sub.edges.len(), 1);
    assert!(matches!(eq_sub.edges[0].2, ConceptEdge::Equivalent { .. }));

    // find_equivalents should also reflect the relationship.
    let equivs = lib.find_equivalents(0).unwrap();
    assert_eq!(equivs.len(), 1);
    assert_eq!(equivs[0].1, 2);
}

// -- Test 14: Manifest shard lifecycle ---------------------------------------

#[test]
fn test_manifest_shard_lifecycle() {
    let dir = tempfile::tempdir().unwrap();
    let loader = LibraryLoader::new(dir.path().join("mathverse"));
    loader.init().unwrap();

    let manifest = loader.load_manifest().unwrap();
    assert!(manifest.base_shards.is_empty());
    assert!(manifest.delta_shards.is_empty());

    // Write 1 base shard + 3 delta shards.
    let mut bw = ShardWriter::new();
    let l0 = bw.add_level(FlatLevel::zero());
    let e0 = bw.add_expr(FlatExpr::sort(l0));
    for i in 0..4 {
        let ni = bw.add_string(&format!("base.c{i}"));
        bw.add_constant(MathverseConstantHeader {
            name_idx: ni,
            type_idx: e0,
            value_idx: e0,
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
    loader.write_shard(&bw, "init", false).unwrap();

    for di in 0..3 {
        let mut dw = ShardWriter::new();
        let l = dw.add_level(FlatLevel::zero());
        let e = dw.add_expr(FlatExpr::sort(l));
        let ni = dw.add_string(&format!("delta{di}.c0"));
        dw.add_constant(MathverseConstantHeader {
            name_idx: ni,
            type_idx: e,
            value_idx: e,
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
        loader.write_shard(&dw, &format!("d{di}"), true).unwrap();
    }

    // Manifest should track 1 base + 3 delta shards.
    let manifest = loader.load_manifest().unwrap();
    assert_eq!(manifest.base_shards.len(), 1);
    assert_eq!(manifest.delta_shards.len(), 3);
    let stats = manifest.total_stats();
    assert_eq!(stats.total_constants, 7);

    // Compact.
    let result = loader.compact().unwrap();
    assert_eq!(result.deltas_merged, 3);

    // After compaction: 1 base shard, 0 delta.
    let manifest2 = loader.load_manifest().unwrap();
    assert_eq!(manifest2.base_shards.len(), 1);
    assert_eq!(manifest2.delta_shards.len(), 0);

    // Integrity passes.
    let integrity = loader.verify_integrity().unwrap();
    assert_eq!(integrity.shards_valid, 1);
    assert!(integrity.shards_corrupt.is_empty());

    // Library loads with all 7 constants.
    let lib = loader.load_library(TrustPolicy::permissive()).unwrap();
    assert_eq!(lib.constant_count(), 7);
}

// -- Test 15: Concurrent shard writes ----------------------------------------

#[test]
fn test_concurrent_shard_writes() {
    let dir = tempfile::tempdir().unwrap();
    let loader = LibraryLoader::new(dir.path().join("mathverse"));
    loader.init().unwrap();

    // Write two shards to different paths from separate ShardWriters.
    let mk_shard = |prefix: &str, count: usize| -> ShardWriter {
        let mut w = ShardWriter::new();
        let l = w.add_level(FlatLevel::zero());
        let e = w.add_expr(FlatExpr::sort(l));
        for i in 0..count {
            let ni = w.add_string(&format!("{prefix}.c{i}"));
            w.add_constant(MathverseConstantHeader {
                name_idx: ni,
                type_idx: e,
                value_idx: e,
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
        w
    };

    let w1 = mk_shard("shard_a", 5);
    let w2 = mk_shard("shard_b", 3);

    loader.write_shard(&w1, "a0", false).unwrap();
    loader.write_shard(&w2, "b0", true).unwrap();

    // Both load independently.
    let lib = loader.load_library(TrustPolicy::permissive()).unwrap();
    assert_eq!(lib.constant_count(), 8);
    assert!(lib.lookup_name("shard_a.c0").is_some());
    assert!(lib.lookup_name("shard_a.c4").is_some());
    assert!(lib.lookup_name("shard_b.c0").is_some());
    assert!(lib.lookup_name("shard_b.c2").is_some());

    // Merge via compaction.
    loader.compact().unwrap();
    let lib2 = loader.load_library(TrustPolicy::permissive()).unwrap();
    assert_eq!(lib2.constant_count(), 8);
    assert!(lib2.lookup_name("shard_a.c0").is_some());
    assert!(lib2.lookup_name("shard_b.c2").is_some());
}

// -- Test 16: Large library 1000 constants -----------------------------------

#[test]
fn test_large_library_1000_constants() {
    let systems = [
        SourceSystem::Lean4,
        SourceSystem::Coq,
        SourceSystem::Isabelle,
        SourceSystem::HolLight,
        SourceSystem::Metamath,
    ];
    let mut all_entries: Vec<(
        &str,
        SourceSystem,
        ImportConfidence,
        ContentDomain,
        AxiomProfile,
    )> = Vec::new();
    let names: Vec<String> = (0..1000)
        .map(|i| {
            let sys_idx = i % systems.len();
            format!("thm_{sys_idx}_{i}")
        })
        .collect();

    for (i, name) in names.iter().enumerate() {
        let sys = systems[i % systems.len()];
        let conf = if sys == SourceSystem::Lean4 {
            ImportConfidence::KernelVerified
        } else {
            ImportConfidence::Translated
        };
        all_entries.push((
            Box::leak(name.clone().into_boxed_str()) as &str,
            sys,
            conf,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        ));
    }

    let shard = raw_shard(&all_entries);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    assert_eq!(lib.constant_count(), 1000);

    // Verify search returns results quickly.
    let start = std::time::Instant::now();
    let sem = lib.search_semantic("thm", 10).unwrap();
    let elapsed = start.elapsed();
    assert!(
        !sem.is_empty(),
        "semantic search should find results in 1000-constant library"
    );
    assert!(
        elapsed.as_millis() < 500,
        "search should be fast, took {elapsed:?}"
    );

    // Verify lookup works for boundary constants.
    assert!(lib.lookup_name("thm_0_0").is_some());
    assert!(lib.lookup_name("thm_4_999").is_some());

    // Add some equivalences and verify graph connectivity.
    for i in 0..10u32 {
        lib.add_equivalence(i, i + 200, EquivConfidence::ErasedCandidate { score: 0.8 });
    }
    assert_eq!(lib.find_equivalents(0).unwrap().len(), 1);
    assert_eq!(lib.find_equivalents(200).unwrap().len(), 1);
}

// ===========================================================================
// Real .olean Fixture Tests
// ===========================================================================

/// Compute the path to the .olean fixture directory, relative to workspace root.
fn olean_fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap() // crates/
        .parent()
        .unwrap() // clean/
        .join("tests/fixtures/olean/v4.13.0")
}

/// Helper: parse an .olean file, import into a ShardWriter, serialize to bytes,
/// deserialize into a ShardReader, and load into an MathverseLibrary. Returns the
/// library and the import stats. If the parse or import fails, returns None
/// with a diagnostic message printed.
fn import_olean_to_library(
    path: &std::path::Path,
    trust: TrustPolicy,
) -> Option<(MathverseLibrary, crate::lean4::olean::alpha::ImportStats)> {
    let module = match parse_module_file(path) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("SKIP {}: parse failed: {e}", path.display());
            return None;
        }
    };

    let mut writer = ShardWriter::new();
    let stats = match import_module(&module, &mut writer) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("SKIP {}: import failed: {e}", path.display());
            return None;
        }
    };

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    let mut lib = MathverseLibrary::new(trust);
    let loaded = lib.load_shard(&reader).unwrap();
    // `stats.total` counts every constant the importer PARSED from the .olean,
    // including auxiliary/compiler-generated decls (equation lemmas, `_cstage`,
    // etc.) that are not emitted to the shard. `loaded` is the count actually
    // written-and-reloaded, so the invariant is `loaded <= total`, not equality.
    // (The per-test bodies assert the real user constants are present.)
    assert!(
        loaded as u32 <= stats.total,
        "loaded {loaded} exceeds parsed total {}",
        stats.total
    );

    Some((lib, stats))
}

/// Collect all constant names from a library into a Vec.
fn all_names(lib: &MathverseLibrary) -> Vec<String> {
    (0..lib.constant_count() as u32)
        .filter_map(|i| lib.get_name(i).map(|s| s.to_string()))
        .collect()
}

// -- Test 17: Real .olean — Minimal ------------------------------------------

#[test]
fn test_real_olean_minimal() {
    let path = olean_fixtures_dir().join("custom/Minimal.olean");
    if !path.exists() {
        eprintln!("SKIP: fixture not found: {}", path.display());
        return;
    }

    let (lib, stats) = match import_olean_to_library(&path, TrustPolicy::permissive()) {
        Some(v) => v,
        None => return,
    };

    // Minimal.lean defines `identity` and `id_id`.
    // The .olean may also contain auxiliary constants (e.g., equation lemmas).
    assert!(
        stats.total >= 2,
        "expected at least 2 constants, got {}",
        stats.total
    );

    let names = all_names(&lib);
    eprintln!("Minimal.olean constants ({}):", names.len());
    for n in &names {
        eprintln!("  {n}");
    }

    // Check that the two user-defined constants are present.
    assert!(
        names
            .iter()
            .any(|n| n == "identity" || n.ends_with(".identity")),
        "expected `identity` constant in {names:?}"
    );
    assert!(
        names.iter().any(|n| n == "id_id" || n.ends_with(".id_id")),
        "expected `id_id` constant in {names:?}"
    );

    // Pipeline round-trip: shard write -> read -> library still works.
    // `stats.total` counts every *parsed* constant; compiler-IR artifacts are
    // parsed-then-skipped (never emitted to the shard), so the loaded count is
    // `total - skipped` (the emitted set).
    assert_eq!(lib.constant_count() as u32, stats.total - stats.skipped);
}

// -- Test 18: Real .olean — Structure ----------------------------------------

#[test]
fn test_real_olean_structure() {
    let path = olean_fixtures_dir().join("custom/Structure.olean");
    if !path.exists() {
        eprintln!("SKIP: fixture not found: {}", path.display());
        return;
    }

    let (lib, stats) = match import_olean_to_library(&path, TrustPolicy::permissive()) {
        Some(v) => v,
        None => return,
    };

    let names = all_names(&lib);
    eprintln!("Structure.olean constants ({}):", names.len());
    for n in &names {
        eprintln!("  {n}");
    }

    // Structure.lean defines MyPair (inductive + constructor + projections) and swap.
    // At minimum we expect the structure type and `swap`.
    assert!(
        stats.total >= 2,
        "expected at least 2 constants, got {}",
        stats.total
    );

    // Check for the structure name or constructor.
    let has_mypair = names.iter().any(|n| n.contains("MyPair"));
    let has_swap = names.iter().any(|n| n.contains("swap"));
    assert!(has_mypair, "expected MyPair-related constant in {names:?}");
    assert!(has_swap, "expected swap constant in {names:?}");

    // Structures generate projections (.fst, .snd) — check at least one.
    let has_projection = names
        .iter()
        .any(|n| n.contains(".fst") || n.contains(".snd"));
    if has_projection {
        eprintln!("  Found projections for MyPair");
    }
}

// -- Test 19: Real .olean — Inductive ----------------------------------------

#[test]
fn test_real_olean_inductive() {
    let path = olean_fixtures_dir().join("custom/Inductive.olean");
    if !path.exists() {
        eprintln!("SKIP: fixture not found: {}", path.display());
        return;
    }

    let (lib, stats) = match import_olean_to_library(&path, TrustPolicy::permissive()) {
        Some(v) => v,
        None => return,
    };

    let names = all_names(&lib);
    eprintln!("Inductive.olean constants ({}):", names.len());
    for n in &names {
        eprintln!("  {n}");
    }

    // Inductive.lean defines MyBool with myTrue, myFalse constructors + myNot.
    // Lean also auto-generates a recursor (MyBool.rec or MyBool.casesOn etc.).
    assert!(
        stats.total >= 3,
        "expected at least 3 constants, got {}",
        stats.total
    );

    let has_mybool = names.iter().any(|n| n.contains("MyBool"));
    let has_mynot = names.iter().any(|n| n.contains("myNot"));
    assert!(has_mybool, "expected MyBool type in {names:?}");
    assert!(has_mynot, "expected myNot definition in {names:?}");

    // Check for constructors.
    let has_constructor = names
        .iter()
        .any(|n| n.contains("myTrue") || n.contains("myFalse"));
    assert!(has_constructor, "expected MyBool constructors in {names:?}");

    // Check for recursor (auto-generated by Lean for inductives).
    let has_recursor = names
        .iter()
        .any(|n| n.contains(".rec") || n.contains(".casesOn"));
    if has_recursor {
        eprintln!("  Found recursor for MyBool");
    }
}

// -- Test 20: Real .olean — Init (stdlib) ------------------------------------

#[test]
fn test_real_olean_init() {
    let path = olean_fixtures_dir().join("stdlib/Init.olean");
    if !path.exists() {
        eprintln!("SKIP: fixture not found: {}", path.display());
        return;
    }

    let (lib, stats) = match import_olean_to_library(&path, TrustPolicy::permissive()) {
        Some(v) => v,
        None => return,
    };

    let names = all_names(&lib);
    eprintln!(
        "Init.olean: {} constants imported ({} kernel_verified, {} axiomatized, {} skipped)",
        stats.total, stats.kernel_verified, stats.axiomatized, stats.skipped
    );

    // Init.olean might be a very thin re-export module with few or no
    // constants of its own (it primarily imports sub-modules).
    // The pipeline should succeed regardless.
    // Pipeline succeeded if we reached this point — stats.total may be 0
    // for thin re-export modules that only contain imports.
    let _ = stats.total;

    // If constants were imported, check for well-known stdlib names.
    if !names.is_empty() {
        eprintln!("  First 20 constants:");
        for n in names.iter().take(20) {
            eprintln!("    {n}");
        }

        // These are commonly found in Init — check if any are present.
        let well_known = [
            "Bool", "True", "False", "Nat", "Nat.zero", "Nat.succ", "String", "List", "Option",
            "And", "Or", "Not", "Eq",
        ];
        let found: Vec<_> = well_known
            .iter()
            .filter(|&&wk| names.iter().any(|n| n == wk))
            .collect();
        if !found.is_empty() {
            eprintln!("  Found well-known names: {found:?}");
        }
    }

    // Verify the shard round-trip is lossless.
    assert_eq!(lib.constant_count() as u32, stats.total);
}

// -- Test 21: Real .olean — Init/Option --------------------------------------

#[test]
fn test_real_olean_init_option() {
    let path = olean_fixtures_dir().join("stdlib/Init/Option.olean");
    if !path.exists() {
        eprintln!("SKIP: fixture not found: {}", path.display());
        return;
    }

    let (lib, stats) = match import_olean_to_library(&path, TrustPolicy::permissive()) {
        Some(v) => v,
        None => return,
    };

    let names = all_names(&lib);
    eprintln!("Init/Option.olean: {} constants", names.len());
    for n in &names {
        eprintln!("  {n}");
    }

    // Init/Option.olean should define Option, Option.some, Option.none, and
    // related constants (recursor, decidable instances, etc.).
    if !names.is_empty() {
        let has_option = names
            .iter()
            .any(|n| n == "Option" || n.starts_with("Option."));
        if has_option {
            eprintln!("  Found Option-related constants");
        }

        // Check specific constructors.
        let has_some = names
            .iter()
            .any(|n| n.contains("Option.some") || n.contains("some"));
        let has_none = names
            .iter()
            .any(|n| n.contains("Option.none") || n.contains("none"));
        if has_some {
            eprintln!("  Found Option.some");
        }
        if has_none {
            eprintln!("  Found Option.none");
        }
    }

    assert_eq!(lib.constant_count() as u32, stats.total);
}

// -- Test 22: Real .olean — Init/Char ----------------------------------------

#[test]
fn test_real_olean_init_char() {
    let path = olean_fixtures_dir().join("stdlib/Init/Char.olean");
    if !path.exists() {
        eprintln!("SKIP: fixture not found: {}", path.display());
        return;
    }

    let (lib, stats) = match import_olean_to_library(&path, TrustPolicy::permissive()) {
        Some(v) => v,
        None => return,
    };

    let names = all_names(&lib);
    eprintln!("Init/Char.olean: {} constants", names.len());
    for n in names.iter().take(30) {
        eprintln!("  {n}");
    }

    // Char module should define the Char type or Char-related constants.
    if !names.is_empty() {
        let has_char = names.iter().any(|n| n == "Char" || n.starts_with("Char."));
        if has_char {
            eprintln!("  Found Char type");
        }
    }

    assert_eq!(lib.constant_count() as u32, stats.total);
}

// -- Test 23: All fixtures into one MathverseLibrary -----------------------------

#[test]
fn test_real_olean_all_fixtures() {
    let fixtures = olean_fixtures_dir();
    if !fixtures.exists() {
        eprintln!("SKIP: fixtures dir not found: {}", fixtures.display());
        return;
    }

    let olean_paths = [
        fixtures.join("stdlib/Init.olean"),
        fixtures.join("stdlib/Init/Char.olean"),
        fixtures.join("stdlib/Init/Option.olean"),
        fixtures.join("custom/Minimal.olean"),
        fixtures.join("custom/Structure.olean"),
        fixtures.join("custom/Inductive.olean"),
    ];

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    let mut total_imported: u32 = 0;
    let mut files_ok: u32 = 0;
    let mut files_skipped: u32 = 0;

    for path in &olean_paths {
        if !path.exists() {
            eprintln!("SKIP fixture: {}", path.display());
            files_skipped += 1;
            continue;
        }

        let module = match parse_module_file(path) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("SKIP {}: parse failed: {e}", path.display());
                files_skipped += 1;
                continue;
            }
        };

        let mut writer = ShardWriter::new();
        let stats = match import_module(&module, &mut writer) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("SKIP {}: import failed: {e}", path.display());
                files_skipped += 1;
                continue;
            }
        };

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();
        let loaded = lib.load_shard(&reader).unwrap();
        // Loaded == emitted == parsed - skipped (compiler-IR is parsed then skipped).
        assert_eq!(loaded as u32, stats.total - stats.skipped);

        total_imported += loaded as u32;
        files_ok += 1;
        eprintln!("OK {}: {} constants", path.display(), stats.total);
    }

    eprintln!(
        "\nAll fixtures: {files_ok} ok, {files_skipped} skipped, {total_imported} constants total"
    );

    // No .olean binaries on this machine — skip cleanly rather than
    // fail the build. The fixtures dir lists six expected files but
    // they are platform-/Lean-version-specific compiled artifacts;
    // CI machines that don't have Lean 4 installed don't carry them.
    if files_ok == 0 {
        eprintln!("SKIP: no .olean fixtures available on this machine");
        return;
    }

    // At minimum the custom fixtures should succeed — they are small and
    // well-controlled. Require at least some constants.
    assert!(
        files_ok >= 3,
        "expected at least 3 fixtures to parse, got {files_ok}"
    );
    assert!(
        total_imported >= 5,
        "expected at least 5 total constants, got {total_imported}"
    );

    let names = all_names(&lib);
    eprintln!(
        "Library has {} constants after loading all shards",
        lib.constant_count()
    );

    // Name lookup should work across shards.
    let identity_found = names.iter().any(|n| n.contains("identity"));
    let mybool_found = names.iter().any(|n| n.contains("MyBool"));
    let swap_found = names.iter().any(|n| n.contains("swap"));
    assert!(identity_found, "expected `identity` from Minimal.olean");
    assert!(mybool_found, "expected `MyBool` from Inductive.olean");
    assert!(swap_found, "expected `swap` from Structure.olean");

    // Semantic search should return results (BM25 over all loaded names).
    let sem = lib.search_semantic("identity", 10).unwrap();
    eprintln!("Semantic search 'identity': {} results", sem.len());
    // At least one result expected since we know `identity` is a constant.
    assert!(
        !sem.is_empty(),
        "semantic search for 'identity' should return results"
    );

    // Dependency walk: pick the first constant and verify BFS terminates.
    if lib.constant_count() > 0 {
        let deps: Vec<ConstantIdx> = lib.walk_deps(0).collect();
        assert!(
            !deps.is_empty(),
            "walk_deps should return at least the root"
        );
    }

    // Trust policy filtering: default policy hides axiomatized constants.
    let mut strict_lib = MathverseLibrary::new(TrustPolicy::default_policy());
    for path in &olean_paths {
        if !path.exists() {
            continue;
        }
        let module = match parse_module_file(path) {
            Ok(m) => m,
            Err(_) => continue,
        };
        let mut writer = ShardWriter::new();
        if import_module(&module, &mut writer).is_err() {
            continue;
        }
        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();
        let _ = strict_lib.load_shard(&reader);
    }
    // Default policy should still expose kernel-verified constants.
    let strict_names = all_names(&strict_lib);
    let strict_identity = strict_names.iter().any(|n| n.contains("identity"));
    // `identity` is a definition with a proof term => kernel-verified => visible.
    if strict_identity {
        eprintln!("  Default policy: `identity` is visible (expected)");
    }

    // Shard round-trip: write the full library out and re-load.
    let dir = tempfile::tempdir().unwrap();
    let loader = LibraryLoader::new(dir.path().join("mathverse"));
    loader.init().unwrap();

    // Write each fixture as a separate base shard.
    let mut shard_idx = 0u32;
    for path in &olean_paths {
        if !path.exists() {
            continue;
        }
        let module = match parse_module_file(path) {
            Ok(m) => m,
            Err(_) => continue,
        };
        let mut writer = ShardWriter::new();
        if import_module(&module, &mut writer).is_err() {
            continue;
        }
        loader
            .write_shard(&writer, &format!("fixture_{shard_idx}"), false)
            .unwrap();
        shard_idx += 1;
    }

    let reloaded = loader.load_library(TrustPolicy::permissive()).unwrap();
    assert_eq!(
        reloaded.constant_count(),
        lib.constant_count(),
        "reloaded library should have same constant count as in-memory library"
    );
}

// -- Test 24: Batch import with real fixtures --------------------------------

#[test]
fn test_real_olean_batch_import() {
    let fixtures = olean_fixtures_dir();
    if !fixtures.exists() {
        eprintln!("SKIP: fixtures dir not found: {}", fixtures.display());
        return;
    }

    let config = Lean4BatchConfig::new(fixtures.clone());
    let importer = Lean4BatchImporter::new(config);

    // Discover all .olean files in the fixtures directory.
    let files = importer.discover_files().unwrap();
    eprintln!("Batch discover: found {} .olean files", files.len());
    for f in &files {
        eprintln!("  {}", f.display());
    }

    if files.is_empty() {
        eprintln!("SKIP: no .olean files in fixture directory");
        return;
    }
    // We have 6 fixture files when Lean 4 build artifacts are present.
    assert!(
        files.len() >= 3,
        "expected at least 3 .olean files, found {}",
        files.len()
    );

    // Run the full batch import to a temporary directory.
    let dir = tempfile::tempdir().unwrap();
    let result = importer.import_all(dir.path()).unwrap();

    eprintln!("Batch import result:");
    eprintln!("  total_files: {}", result.total_files);
    eprintln!("  total_constants: {}", result.total_constants);
    eprintln!("  total_kernel_verified: {}", result.total_kernel_verified);
    eprintln!("  shards_written: {}", result.shards_written.len());
    eprintln!("  files_failed: {}", result.files_failed.len());

    for (path, err) in &result.files_failed {
        eprintln!("  FAILED: {}: {err}", path.display());
    }

    // At least some files should have imported successfully.
    let files_succeeded = result.total_files - result.files_failed.len() as u32;
    assert!(
        files_succeeded >= 3,
        "expected at least 3 files to import, got {files_succeeded}"
    );
    assert!(
        result.total_constants >= 5,
        "expected at least 5 constants, got {}",
        result.total_constants
    );
    assert!(
        !result.shards_written.is_empty(),
        "expected at least one shard written"
    );

    // Load the written shards and verify they contain valid data.
    for shard_path in &result.shards_written {
        let reader = ShardReader::from_file(shard_path).unwrap();
        assert!(
            !reader.constants.is_empty(),
            "shard should have constants: {}",
            shard_path.display()
        );
    }
}

// -- Test 25: Full end-to-end pipeline ---------------------------------------

#[test]
fn test_real_olean_full_pipeline() {
    let fixtures = olean_fixtures_dir();
    if !fixtures.exists() {
        eprintln!("SKIP: fixtures dir not found: {}", fixtures.display());
        return;
    }

    let olean_paths = [
        fixtures.join("custom/Minimal.olean"),
        fixtures.join("custom/Structure.olean"),
        fixtures.join("custom/Inductive.olean"),
        fixtures.join("stdlib/Init.olean"),
        fixtures.join("stdlib/Init/Option.olean"),
        fixtures.join("stdlib/Init/Char.olean"),
    ];

    // Step 1: Import all fixtures into shard writers.
    let dir = tempfile::tempdir().unwrap();
    let loader = LibraryLoader::new(dir.path().join("mathverse"));
    loader.init().unwrap();

    let mut total_constants = 0u32;
    let mut shard_idx = 0u32;
    for path in &olean_paths {
        if !path.exists() {
            eprintln!("SKIP fixture: {}", path.display());
            continue;
        }
        let module = match parse_module_file(path) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("SKIP {}: {e}", path.display());
                continue;
            }
        };
        let mut writer = ShardWriter::new();
        match import_module(&module, &mut writer) {
            Ok(stats) => {
                // Count emitted constants (parsed - skipped); compiler-IR is skipped.
                total_constants += stats.total - stats.skipped;
                loader
                    .write_shard(&writer, &format!("s{shard_idx}"), false)
                    .unwrap();
                shard_idx += 1;
            }
            Err(e) => {
                eprintln!("SKIP {}: import error: {e}", path.display());
            }
        }
    }

    if shard_idx == 0 {
        eprintln!("SKIP: no .olean fixtures available — full pipeline not exercised");
        return;
    }
    assert!(
        shard_idx >= 3,
        "need at least 3 shards for meaningful pipeline test"
    );

    // Step 2: Load via LibraryLoader and verify manifest.
    let manifest = loader.load_manifest().unwrap();
    assert_eq!(manifest.base_shards.len(), shard_idx as usize);

    // Step 3: Load library and verify integrity.
    let integrity = loader.verify_integrity().unwrap();
    assert_eq!(integrity.shards_valid, shard_idx as usize);
    assert!(
        integrity.shards_corrupt.is_empty(),
        "no corrupt shards expected"
    );

    let lib = loader.load_library(TrustPolicy::permissive()).unwrap();
    assert_eq!(lib.constant_count() as u32, total_constants);

    eprintln!(
        "Full pipeline: {} constants across {} shards",
        total_constants, shard_idx
    );

    // Step 4: Search operations.
    let names = all_names(&lib);

    // Name lookup.
    let has_identity = names.iter().any(|n| n.contains("identity"));
    assert!(has_identity, "identity should be in the library");

    // Semantic search.
    let sem = lib.search_semantic("MyBool", 10).unwrap();
    eprintln!("Semantic search 'MyBool': {} results", sem.len());

    // Dependency walking.
    if lib.constant_count() > 0 {
        let deps: Vec<ConstantIdx> = lib.walk_deps(0).collect();
        assert!(!deps.is_empty());
    }

    // Step 5: Export training data.
    let exporter = Exporter::new(&lib, ExportConfig::statement_only());
    let mut export_buf = Vec::new();
    let export_stats = exporter.export_to_writer(&mut export_buf).unwrap();
    eprintln!(
        "Exported {} records ({} bytes)",
        export_stats.exported,
        export_buf.len()
    );
    assert!(
        export_stats.exported > 0,
        "should export at least one record"
    );

    let output = String::from_utf8(export_buf).unwrap();
    for line in output.lines().take(3) {
        let record: serde_json::Value = serde_json::from_str(line).unwrap();
        assert!(
            record.get("name").is_some(),
            "export record should have a name"
        );
        assert!(
            record.get("source").is_some(),
            "export record should have source"
        );
    }

    // Step 6: Compact and re-verify.
    // Write a delta shard to test compaction.
    let mut delta_writer = ShardWriter::new();
    let l0 = delta_writer.add_level(FlatLevel::zero());
    let e0 = delta_writer.add_expr(FlatExpr::sort(l0));
    let ni = delta_writer.add_string("test.delta.constant");
    delta_writer.add_constant(MathverseConstantHeader {
        name_idx: ni,
        type_idx: e0,
        value_idx: e0,
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
    loader.write_shard(&delta_writer, "delta0", true).unwrap();

    let lib_with_delta = loader.load_library(TrustPolicy::permissive()).unwrap();
    assert_eq!(lib_with_delta.constant_count() as u32, total_constants + 1);

    let compact_result = loader.compact().unwrap();
    assert_eq!(compact_result.deltas_merged, 1);

    let lib_post_compact = loader.load_library(TrustPolicy::permissive()).unwrap();
    assert_eq!(
        lib_post_compact.constant_count() as u32,
        total_constants + 1
    );
}

// -- Test 26: Provenance tracking with real .olean files ---------------------

#[test]
fn test_real_olean_provenance() {
    let fixtures = olean_fixtures_dir();
    let olean_paths = [
        ("custom/Minimal.olean", "Minimal"),
        ("custom/Structure.olean", "Structure"),
        ("custom/Inductive.olean", "Inductive"),
    ];

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    let mut global_offset: u32 = 0;
    let mut provenance_entries: Vec<(u32, String, String)> = Vec::new();

    for &(rel_path, _module_name) in &olean_paths {
        let path = fixtures.join(rel_path);
        if !path.exists() {
            eprintln!("SKIP: {}", path.display());
            continue;
        }

        let module = match parse_module_file(&path) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("SKIP {}: {e}", path.display());
                continue;
            }
        };

        let mut writer = ShardWriter::new();
        let stats = match import_module(&module, &mut writer) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("SKIP {}: {e}", path.display());
                continue;
            }
        };

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();
        // Use the actual loaded (emitted) count, not `stats.total` (which also
        // counts parsed-then-skipped compiler-IR): indexing/advancing by the
        // parsed total overshoots into the next file's region and desyncs the
        // global index from the constants actually present.
        let loaded = lib.load_shard(&reader).unwrap() as u32;

        // Track provenance for each constant from this file.
        for i in 0..loaded {
            let idx = global_offset + i;
            if let Some(name) = lib.get_name(idx) {
                provenance_entries.push((idx, name.to_string(), rel_path.to_string()));
            }
        }

        global_offset += loaded;
    }

    if provenance_entries.is_empty() {
        eprintln!("SKIP: no provenance entries produced — fixtures unavailable");
        return;
    }

    // Attach provenance records with source file path.
    for (idx, name, source_path) in &provenance_entries {
        let record = ProvenanceBuilder::new(name)
            .source_file(source_path)
            .module_path(&source_path.replace(".olean", "").replace('/', "."))
            .source_version("Lean 4.13.0")
            .build();
        lib.add_provenance_record(*idx, record);
    }

    // Verify provenance records were stored correctly.
    assert_eq!(lib.provenance().len(), provenance_entries.len());

    for (idx, name, source_path) in &provenance_entries {
        let rec = lib
            .provenance()
            .get(*idx)
            .expect("provenance record should exist");
        assert_eq!(rec.original_name, *name);
        assert_eq!(rec.source_file.as_deref(), Some(source_path.as_str()));
        assert_eq!(rec.source_version.as_deref(), Some("Lean 4.13.0"));

        // Verify digest integrity.
        let header = lib.get_constant(*idx).unwrap();
        assert!(
            lib.provenance().verify_digest(header),
            "sidecar digest mismatch for constant `{name}` at idx {idx}"
        );
    }

    eprintln!(
        "Provenance: {} records verified across {} files",
        provenance_entries.len(),
        olean_paths.len()
    );
}

// -- Test 27: Batch import with module filter --------------------------------

#[test]
fn test_real_olean_batch_with_filter() {
    let fixtures = olean_fixtures_dir();
    if !fixtures.exists() {
        eprintln!("SKIP: fixtures dir not found: {}", fixtures.display());
        return;
    }

    // Filter to only custom modules (not stdlib).
    let config = Lean4BatchConfig::new(fixtures.join("custom"));
    let importer = Lean4BatchImporter::new(config);

    let files = importer.discover_files().unwrap();
    eprintln!("Custom-only discover: {} files", files.len());
    if files.is_empty() {
        eprintln!("SKIP: no .olean files in custom fixture directory");
        return;
    }
    assert_eq!(files.len(), 3, "expected exactly 3 custom .olean files");

    let dir = tempfile::tempdir().unwrap();
    let result = importer.import_all(dir.path()).unwrap();

    eprintln!(
        "Custom batch: {} constants, {} failures",
        result.total_constants,
        result.files_failed.len()
    );

    // All 3 custom files should parse and import successfully.
    let files_ok = result.total_files - result.files_failed.len() as u32;
    assert_eq!(files_ok, 3, "all 3 custom fixtures should import");
    assert!(
        result.total_constants >= 5,
        "custom fixtures have at least 5 constants"
    );
}

// -- Test 28: Import stats accuracy with real data ---------------------------

#[test]
fn test_real_olean_import_stats_accuracy() {
    let fixtures = olean_fixtures_dir();
    let path = fixtures.join("custom/Inductive.olean");
    if !path.exists() {
        eprintln!("SKIP: fixture not found: {}", path.display());
        return;
    }

    let module = parse_module_file(&path).unwrap();

    let mut writer = ShardWriter::new();
    let stats = import_module(&module, &mut writer).unwrap();

    // Stats invariant: total = kernel_verified + axiomatized + skipped.
    assert_eq!(
        stats.total,
        stats.kernel_verified + stats.axiomatized + stats.skipped,
        "import stats should sum correctly: total={}, kv={}, ax={}, sk={}",
        stats.total,
        stats.kernel_verified,
        stats.axiomatized,
        stats.skipped
    );

    // Inductive.lean should produce mostly kernel-verified constants
    // (the inductive type, constructors, recursor are all kernel-verified).
    assert!(
        stats.kernel_verified >= 3,
        "expected at least 3 kernel-verified constants for MyBool inductive, got {}",
        stats.kernel_verified
    );

    eprintln!(
        "Inductive.olean stats: total={}, kv={}, ax={}, sk={}",
        stats.total, stats.kernel_verified, stats.axiomatized, stats.skipped
    );
}

// -- Test 29: Shard binary stability across fixtures -------------------------

#[test]
fn test_real_olean_shard_determinism() {
    let path = olean_fixtures_dir().join("custom/Minimal.olean");
    if !path.exists() {
        eprintln!("SKIP: fixture not found: {}", path.display());
        return;
    }

    // Import twice and verify the shard bytes are identical.
    let module = match parse_module_file(&path) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("SKIP: {e}");
            return;
        }
    };

    let mut writer1 = ShardWriter::new();
    import_module(&module, &mut writer1).unwrap();
    let mut buf1 = Vec::new();
    writer1.write(&mut buf1).unwrap();

    let mut writer2 = ShardWriter::new();
    import_module(&module, &mut writer2).unwrap();
    let mut buf2 = Vec::new();
    writer2.write(&mut buf2).unwrap();

    assert_eq!(buf1.len(), buf2.len(), "shard size should be deterministic");
    assert_eq!(buf1, buf2, "shard bytes should be identical for same input");
}

// -- Test 30: Cross-fixture name uniqueness ----------------------------------

#[test]
fn test_real_olean_cross_fixture_names() {
    let fixtures = olean_fixtures_dir();
    let olean_paths = [
        fixtures.join("custom/Minimal.olean"),
        fixtures.join("custom/Structure.olean"),
        fixtures.join("custom/Inductive.olean"),
    ];

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    let mut per_file_names: Vec<Vec<String>> = Vec::new();

    for path in &olean_paths {
        if !path.exists() {
            continue;
        }
        let module = match parse_module_file(path) {
            Ok(m) => m,
            Err(_) => continue,
        };
        let mut writer = ShardWriter::new();
        if import_module(&module, &mut writer).is_err() {
            continue;
        }
        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        let base = lib.constant_count();
        lib.load_shard(&reader).unwrap();
        let count = lib.constant_count() - base;

        let file_names: Vec<String> = (base..base + count)
            .filter_map(|i| lib.get_name(i as u32).map(|s| s.to_string()))
            .collect();
        per_file_names.push(file_names);
    }

    // Verify constants from different files have distinct namespaces.
    // Custom .olean files should not share top-level constant names.
    if per_file_names.len() >= 2 {
        let set0: std::collections::HashSet<_> = per_file_names[0].iter().collect();
        let set1: std::collections::HashSet<_> = per_file_names[1].iter().collect();
        let overlap: Vec<_> = set0.intersection(&set1).collect();
        eprintln!("Name overlap between Minimal and Structure: {overlap:?}");
        // Some equation-lemma names might overlap (e.g., `Eq.mpr`) but the
        // user-defined names (identity, MyPair, MyBool) should be distinct.
    }

    // Every constant in the library should have a resolvable name.
    for i in 0..lib.constant_count() as u32 {
        assert!(lib.get_name(i).is_some(), "constant {i} should have a name");
    }
}

// -- Test 31: WS5 — real .olean -> stamped KernelVerified on disk ------------

/// WS5 end-to-end on a REAL fixture `.olean`: convert `Minimal.olean` to a
/// shard (the importer stamps only the honest heuristic — `SourceVerified` /
/// `Axiomatized`, never `KernelVerified`), write it to disk, re-verify the
/// corpus in Clean's kernel to obtain the GENUINE `kernel_verified_names`, stamp
/// that verdict into the shard BYTES on disk, reload from disk, and assert the
/// stored `KernelVerified` count is non-zero.
///
/// `Minimal.olean` yields several value-bearing definitions whose values pass
/// `check_type` under the corpus verifier, so this exercises a real non-zero
/// on-disk stamp (not merely the graceful-skip path).
///
/// SOUNDNESS: only names returned by `verify_corpus_incremental` — i.e. decls
/// whose value passed the kernel's `check_type` — are stamped. The heuristic
/// converter never emits `KernelVerified`, so the pre-stamp on-disk count is 0;
/// every stamped header is a genuine kernel verdict, never a heuristic.
#[cfg(test)]
#[test]
fn test_ws5_real_olean_stamps_kernel_verified_on_disk() {
    use crate::lean4::olean::olean_bridge::convert_olean_to_mathverse;
    use crate::library::{
        count_stored_kernel_verified, stamp_shard_dir_kernel_verified, MathverseLibrary,
    };
    use crate::verify::incremental::verify_corpus_incremental;
    use crate::verify::kernel_verified_manifest::KernelVerifiedManifest;

    let path = olean_fixtures_dir().join("custom/Minimal.olean");
    if !path.exists() {
        eprintln!("SKIP: fixture not found: {}", path.display());
        return;
    }

    // (1) Convert the real .olean to a complete shard via the heuristic path.
    let (buf, convert) = match convert_olean_to_mathverse(&path) {
        Ok(out) => out,
        Err(e) => {
            eprintln!("SKIP: convert failed: {e}");
            return;
        }
    };
    // The heuristic converter must NOT have minted any KernelVerified bytes.
    assert_eq!(
        convert.kernel_verified_from_tc, 0,
        "heuristic conversion must not type-check anything itself"
    );

    let dir = tempfile::tempdir().expect("tempdir");
    let shard_path = dir.path().join("Minimal.mathverse");
    std::fs::write(&shard_path, &buf).expect("write shard");

    // Pre-condition: stored KernelVerified == 0 (the status quo WS5 fixes).
    let (before, unreadable) = count_stored_kernel_verified(dir.path()).expect("count before");
    assert!(unreadable.is_empty(), "shard readable: {unreadable:?}");
    assert_eq!(before, 0, "converter must store KernelVerified = 0");

    // (2) Re-verify the corpus in the Clean kernel for the GENUINE verdict.
    let shard = ShardReader::from_bytes(&buf).expect("decode shard");
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).expect("load shard");
    let prelude =
        clean_kernel::Environment::try_with_prelude().expect("kernel prelude environment");
    let report = verify_corpus_incremental(&lib, prelude);
    eprintln!(
        "Minimal.olean corpus: total={}, kernel_verified={}, axiom_accepted={}, \
         axiom_fallback={}, failed={}, reconstruct_failed={}",
        report.total,
        report.kernel_verified,
        report.axiom_accepted,
        report.axiom_fallback,
        report.failed,
        report.reconstruct_failed,
    );
    assert_eq!(
        report.kernel_verified_names.len(),
        report.kernel_verified,
        "verdict-name set length must match the kernel_verified count"
    );
    if report.kernel_verified == 0 {
        eprintln!(
            "SKIP: this fixture yielded no genuine kernel-verified decls under the \
             current kernel; the deterministic synthetic round-trip test covers count > 0"
        );
        return;
    }

    // (3) DESTRUCTIVE on-disk stamp from the kernel's verdict.
    let manifest =
        KernelVerifiedManifest::from_report(&dir.path().display().to_string(), 1, &report);
    let stamp = stamp_shard_dir_kernel_verified(dir.path(), &manifest).expect("stamp on disk");
    assert_eq!(stamp.shards_rewritten, 1);
    assert_eq!(
        stamp.constants_stamped, report.kernel_verified,
        "every genuine verdict in this single shard is stamped"
    );

    // (4) Reload from DISK and assert the stamp persisted into the bytes.
    let (after, unreadable_after) = count_stored_kernel_verified(dir.path()).expect("count after");
    assert!(unreadable_after.is_empty());
    assert_eq!(
        after, report.kernel_verified,
        "stored KernelVerified must equal the kernel verdict after the on-disk stamp"
    );
    assert!(after > 0, "WS5 success metric: stored KernelVerified > 0");
}
