// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_olean::expr::{ParsedBinderInfo, ParsedExpr};
use clean_olean::level::ParsedLevel;
use clean_olean::module::{ConstantKind, ParsedConstant, ParsedModule};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn mock_module_ap(constants: Vec<ParsedConstant>) -> ParsedModule {
    ParsedModule {
        const_names: constants.iter().map(|c| c.name.clone()).collect(),
        constants,
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    }
}

fn mock_constant_ap(name: &str, kind: ConstantKind, has_val: bool) -> ParsedConstant {
    ParsedConstant {
        definition_safety: None,
        quot_kind: None,
        name: name.to_string(),
        kind,
        level_params: Vec::new(),
        type_: None,
        value: if has_val {
            Some(ParsedExpr::Sort(ParsedLevel::Zero))
        } else {
            None
        },
        inductive_val: None,
        constructor_val: None,
        recursor_val: None,
        hints: None,
    }
}

fn constant_with_deps_ap(name: &str, kind: ConstantKind, dep_names: &[&str]) -> ParsedConstant {
    // Build a type expr that references all dep_names via Const nodes.
    let mut expr: ParsedExpr = ParsedExpr::Sort(ParsedLevel::Zero);
    for dep in dep_names {
        expr = ParsedExpr::App(
            Box::new(ParsedExpr::Const(dep.to_string(), vec![])),
            Box::new(expr),
        );
    }
    ParsedConstant {
        definition_safety: None,
        quot_kind: None,
        name: name.to_string(),
        kind,
        level_params: Vec::new(),
        type_: Some(expr),
        value: None,
        inductive_val: None,
        constructor_val: None,
        recursor_val: None,
        hints: None,
    }
}

// ---------------------------------------------------------------------------
// Per-constant profile tests
// ---------------------------------------------------------------------------

#[test]
fn test_choice_profile() {
    let c = mock_constant_ap("Classical.choice", ConstantKind::Axiom, false);
    let profile = compute_lean4_axiom_profile(&c);
    assert!(profile.has(AxiomProfile::CHOICE));
    assert!(profile.has(AxiomProfile::CLASSICAL));
    assert!(profile.has(AxiomProfile::AXIOMATIZED));
}

#[test]
fn test_em_profile() {
    let c = mock_constant_ap("Classical.em", ConstantKind::Axiom, false);
    let profile = compute_lean4_axiom_profile(&c);
    assert!(profile.has(AxiomProfile::LEM));
    assert!(profile.has(AxiomProfile::AXIOMATIZED));
}

#[test]
fn test_propext_profile() {
    let c = mock_constant_ap("propext", ConstantKind::Axiom, false);
    let profile = compute_lean4_axiom_profile(&c);
    assert!(profile.has(AxiomProfile::PROP_EXT));
    assert!(profile.has(AxiomProfile::AXIOMATIZED));
    assert!(!profile.has(AxiomProfile::CHOICE));
}

#[test]
fn test_funext_profile() {
    let c = mock_constant_ap("funext", ConstantKind::Axiom, false);
    let profile = compute_lean4_axiom_profile(&c);
    assert!(profile.has(AxiomProfile::FUNC_EXT));
    assert!(profile.has(AxiomProfile::AXIOMATIZED));
}

#[test]
fn test_quot_variants_profile() {
    for name in &["Quot", "Quot.mk", "Quot.ind", "Quot.lift", "Quot.sound"] {
        let c = mock_constant_ap(name, ConstantKind::Quot, false);
        let profile = compute_lean4_axiom_profile(&c);
        assert!(
            profile.has(AxiomProfile::QUOT),
            "{name} should have QUOT bit"
        );
    }
}

#[test]
fn test_theorem_pure_profile() {
    let c = mock_constant_ap("Nat.add_comm", ConstantKind::Theorem, true);
    let profile = compute_lean4_axiom_profile(&c);
    assert!(profile.is_pure());
}

#[test]
fn test_opaque_axiomatized_profile() {
    let c = mock_constant_ap("SomeOpaque", ConstantKind::Opaque, false);
    let profile = compute_lean4_axiom_profile(&c);
    assert!(profile.has(AxiomProfile::AXIOMATIZED));
    assert!(profile.is_trust_gated());
}

#[test]
fn test_definition_no_axiom_bits() {
    let c = mock_constant_ap("Nat.add", ConstantKind::Definition, true);
    let profile = compute_lean4_axiom_profile(&c);
    assert!(profile.is_pure());
    assert!(!profile.is_trust_gated());
}

#[test]
fn test_inductive_no_axiom_bits() {
    let c = mock_constant_ap("Nat", ConstantKind::Inductive, false);
    let profile = compute_lean4_axiom_profile(&c);
    assert!(profile.is_pure());
}

// ---------------------------------------------------------------------------
// Dependency extraction tests
// ---------------------------------------------------------------------------

#[test]
fn test_extract_deps_empty_constant() {
    let c = mock_constant_ap("x", ConstantKind::Theorem, false);
    let deps = extract_constant_deps(&c);
    assert!(deps.is_empty());
}

#[test]
fn test_extract_deps_from_type_expr() {
    let c = constant_with_deps_ap("foo", ConstantKind::Definition, &["Nat", "Bool"]);
    let deps = extract_constant_deps(&c);
    assert!(deps.contains(&"Nat".to_string()));
    assert!(deps.contains(&"Bool".to_string()));
}

#[test]
fn test_extract_deps_from_value_expr() {
    let val_expr = ParsedExpr::App(
        Box::new(ParsedExpr::Const("Classical.choice".to_string(), vec![])),
        Box::new(ParsedExpr::BVar(0)),
    );
    let c = ParsedConstant {
        definition_safety: None,
        quot_kind: None,
        name: "uses_choice".to_string(),
        kind: ConstantKind::Theorem,
        level_params: Vec::new(),
        type_: None,
        value: Some(val_expr),
        inductive_val: None,
        constructor_val: None,
        recursor_val: None,
        hints: None,
    };
    let deps = extract_constant_deps(&c);
    assert!(deps.contains(&"Classical.choice".to_string()));
}

#[test]
fn test_extract_deps_deduplicates() {
    let expr = ParsedExpr::App(
        Box::new(ParsedExpr::Const("Nat".to_string(), vec![])),
        Box::new(ParsedExpr::Const("Nat".to_string(), vec![])),
    );
    let c = ParsedConstant {
        definition_safety: None,
        quot_kind: None,
        name: "x".to_string(),
        kind: ConstantKind::Definition,
        level_params: Vec::new(),
        type_: Some(expr),
        value: None,
        inductive_val: None,
        constructor_val: None,
        recursor_val: None,
        hints: None,
    };
    let deps = extract_constant_deps(&c);
    assert_eq!(deps.len(), 1);
    assert_eq!(deps[0], "Nat");
}

#[test]
fn test_extract_deps_nested_lam_forall_let() {
    let inner = ParsedExpr::LetE(
        "x".to_string(),
        Box::new(ParsedExpr::Const("Bool".to_string(), vec![])),
        Box::new(ParsedExpr::BVar(0)),
        Box::new(ParsedExpr::Const("List".to_string(), vec![])),
        false,
    );
    let forall = ParsedExpr::ForallE(
        "n".to_string(),
        Box::new(ParsedExpr::Const("Nat".to_string(), vec![])),
        Box::new(inner),
        ParsedBinderInfo::Default,
    );
    let lam = ParsedExpr::Lam(
        "f".to_string(),
        Box::new(ParsedExpr::Sort(ParsedLevel::Zero)),
        Box::new(forall),
        ParsedBinderInfo::Default,
    );
    let c = ParsedConstant {
        definition_safety: None,
        quot_kind: None,
        name: "complex".to_string(),
        kind: ConstantKind::Definition,
        level_params: Vec::new(),
        type_: Some(lam),
        value: None,
        inductive_val: None,
        constructor_val: None,
        recursor_val: None,
        hints: None,
    };
    let deps = extract_constant_deps(&c);
    assert!(deps.contains(&"Nat".to_string()));
    assert!(deps.contains(&"Bool".to_string()));
    assert!(deps.contains(&"List".to_string()));
}

#[test]
fn test_extract_deps_mdata_proj_transparent() {
    let inner = ParsedExpr::Const("Inner".to_string(), vec![]);
    let mdata = ParsedExpr::MData(Box::new(inner));
    let proj = ParsedExpr::Proj("Prod".to_string(), 0, Box::new(mdata));
    let c = ParsedConstant {
        definition_safety: None,
        quot_kind: None,
        name: "x".to_string(),
        kind: ConstantKind::Definition,
        level_params: Vec::new(),
        type_: Some(proj),
        value: None,
        inductive_val: None,
        constructor_val: None,
        recursor_val: None,
        hints: None,
    };
    let deps = extract_constant_deps(&c);
    assert!(deps.contains(&"Inner".to_string()));
}

// ---------------------------------------------------------------------------
// Transitive closure tests
// ---------------------------------------------------------------------------

#[test]
fn test_transitive_profile_direct_axiom() {
    let module = mock_module_ap(vec![mock_constant_ap(
        "Classical.choice",
        ConstantKind::Axiom,
        false,
    )]);
    let profiles = compute_transitive_axiom_profiles(&module);
    let p = profiles
        .get("Classical.choice")
        .copied()
        .unwrap_or_default();
    assert!(p.has(AxiomProfile::CHOICE));
    assert!(p.has(AxiomProfile::AXIOMATIZED));
}

#[test]
fn test_transitive_profile_one_hop() {
    let module = mock_module_ap(vec![
        mock_constant_ap("Classical.choice", ConstantKind::Axiom, false),
        constant_with_deps_ap("A", ConstantKind::Theorem, &["Classical.choice"]),
    ]);
    let profiles = compute_transitive_axiom_profiles(&module);
    let pa = profiles.get("A").copied().unwrap_or_default();
    assert!(pa.has(AxiomProfile::CHOICE));
    assert!(pa.has(AxiomProfile::CLASSICAL));
}

#[test]
fn test_transitive_profile_two_hops() {
    let module = mock_module_ap(vec![
        mock_constant_ap("propext", ConstantKind::Axiom, false),
        constant_with_deps_ap("A", ConstantKind::Definition, &["propext"]),
        constant_with_deps_ap("B", ConstantKind::Theorem, &["A"]),
    ]);
    let profiles = compute_transitive_axiom_profiles(&module);
    let pb = profiles.get("B").copied().unwrap_or_default();
    assert!(pb.has(AxiomProfile::PROP_EXT));
}

#[test]
fn test_transitive_profile_multiple_axioms() {
    let module = mock_module_ap(vec![
        mock_constant_ap("Classical.choice", ConstantKind::Axiom, false),
        mock_constant_ap("propext", ConstantKind::Axiom, false),
        constant_with_deps_ap("A", ConstantKind::Definition, &["Classical.choice"]),
        constant_with_deps_ap("B", ConstantKind::Definition, &["propext"]),
        constant_with_deps_ap("C", ConstantKind::Theorem, &["A", "B"]),
    ]);
    let profiles = compute_transitive_axiom_profiles(&module);
    let pc = profiles.get("C").copied().unwrap_or_default();
    assert!(pc.has(AxiomProfile::CHOICE));
    assert!(pc.has(AxiomProfile::PROP_EXT));
}

#[test]
fn test_transitive_profile_pure_stays_pure() {
    let module = mock_module_ap(vec![
        mock_constant_ap("Nat", ConstantKind::Inductive, false),
        constant_with_deps_ap("Nat.succ", ConstantKind::Constructor, &["Nat"]),
        constant_with_deps_ap("simple_thm", ConstantKind::Theorem, &["Nat", "Nat.succ"]),
    ]);
    let profiles = compute_transitive_axiom_profiles(&module);
    let p = profiles.get("simple_thm").copied().unwrap_or_default();
    assert!(p.is_pure());
}

#[test]
fn test_transitive_profile_external_dep_ignored() {
    let module = mock_module_ap(vec![constant_with_deps_ap(
        "A",
        ConstantKind::Theorem,
        &["ExternalConst"],
    )]);
    let profiles = compute_transitive_axiom_profiles(&module);
    let pa = profiles.get("A").copied().unwrap_or_default();
    assert!(pa.is_pure());
}

#[test]
fn test_transitive_profile_empty_module() {
    let module = mock_module_ap(vec![]);
    let profiles = compute_transitive_axiom_profiles(&module);
    assert!(profiles.is_empty());
}

// ---------------------------------------------------------------------------
// Multi-module transitive closure tests
// ---------------------------------------------------------------------------

#[test]
fn test_transitive_multi_module_cross_dep() {
    let m1 = mock_module_ap(vec![mock_constant_ap(
        "propext",
        ConstantKind::Axiom,
        false,
    )]);
    let m2 = mock_module_ap(vec![constant_with_deps_ap(
        "A",
        ConstantKind::Theorem,
        &["propext"],
    )]);
    let profiles = compute_transitive_profiles_multi(&[&m1, &m2]);
    let pa = profiles.get("A").copied().unwrap_or_default();
    assert!(pa.has(AxiomProfile::PROP_EXT));
}

// ---------------------------------------------------------------------------
// Profile statistics tests
// ---------------------------------------------------------------------------

#[test]
fn test_profile_stats_basic() {
    let module = mock_module_ap(vec![
        mock_constant_ap("Classical.choice", ConstantKind::Axiom, false),
        mock_constant_ap("propext", ConstantKind::Axiom, false),
        mock_constant_ap("Nat.add", ConstantKind::Definition, true),
        mock_constant_ap("Quot", ConstantKind::Quot, false),
    ]);
    let stats = compute_profile_stats(&module);
    assert_eq!(stats.total, 4);
    assert_eq!(stats.pure_count, 1); // Nat.add
    assert_eq!(stats.classical_count, 1); // Classical.choice
    assert_eq!(stats.prop_ext_count, 1); // propext
    assert_eq!(stats.quot_count, 1); // Quot
    assert_eq!(stats.trust_gated_count, 2); // Classical.choice, propext (AXIOMATIZED)
}

#[test]
fn test_profile_stats_empty() {
    let module = mock_module_ap(vec![]);
    let stats = compute_profile_stats(&module);
    assert_eq!(stats.total, 0);
    assert_eq!(stats.pure_count, 0);
}

#[test]
fn test_profile_stats_all_pure() {
    let module = mock_module_ap(vec![
        mock_constant_ap("x", ConstantKind::Theorem, true),
        mock_constant_ap("y", ConstantKind::Definition, true),
        mock_constant_ap("z", ConstantKind::Inductive, false),
    ]);
    let stats = compute_profile_stats(&module);
    assert_eq!(stats.total, 3);
    assert_eq!(stats.pure_count, 3);
    assert_eq!(stats.classical_count, 0);
    assert_eq!(stats.trust_gated_count, 0);
}

// ---------------------------------------------------------------------------
// Shard-level transitive closure tests (the production import path)
//
// These exercise `propagate_shard_axiom_profiles` over a real lowered shard
// produced by the importer, which is what the production conversion path uses.
// Before this closure pass the importer recorded only each constant's *local*
// axiom usage, so a theorem that used an axiom through a chain of intermediate
// definitions was written with `AxiomProfile::NONE`. The regression test below
// pins exactly that pre-closure behavior so the fix cannot silently regress.
// ---------------------------------------------------------------------------

/// Lower a module into a `ShardWriter` and return (writer-bytes-reader-ready)
/// `(constants, exprs, strings)` *before* any transitive closure has run.
fn lower_to_shard_parts(
    module: &ParsedModule,
) -> (
    Vec<crate::types::MathverseConstantHeader>,
    Vec<clean_kernel::flat::FlatExpr>,
    Vec<String>,
) {
    let mut writer = crate::shard::ShardWriter::new();
    crate::lean4::olean::alpha::import_module(module, &mut writer).expect("import should succeed");
    let mut buf = Vec::new();
    writer.write(&mut buf).expect("write should succeed");
    let reader = crate::shard::ShardReader::from_bytes(&buf).expect("read should succeed");
    (reader.constants, reader.exprs, reader.strings)
}

/// Find a constant header by name in a lowered shard.
fn find_const<'a>(
    constants: &'a [crate::types::MathverseConstantHeader],
    strings: &[String],
    name: &str,
) -> &'a crate::types::MathverseConstantHeader {
    constants
        .iter()
        .find(|c| strings.get(c.name_idx as usize).map(String::as_str) == Some(name))
        .unwrap_or_else(|| panic!("constant {name} not found in shard"))
}

#[test]
fn test_shard_closure_two_hop_captures_transitive_axiom() {
    // Classical.choice (axiom) <- mid (def uses it) <- top (theorem uses mid).
    let module = mock_module_ap(vec![
        mock_constant_ap("Classical.choice", ConstantKind::Axiom, false),
        constant_with_deps_ap("mid", ConstantKind::Definition, &["Classical.choice"]),
        constant_with_deps_ap("top", ConstantKind::Theorem, &["mid"]),
    ]);

    let (mut constants, exprs, strings) = lower_to_shard_parts(&module);

    // REGRESSION: the per-constant (local) importer leaves `top` and `mid`
    // looking pure — this is exactly the soundness gap the audit flagged.
    let top_before = find_const(&constants, &strings, "top").axiom_profile;
    let mid_before = find_const(&constants, &strings, "mid").axiom_profile;
    assert!(
        top_before.is_pure(),
        "pre-closure: local importer mislabels `top` as pure (the bug)"
    );
    assert!(
        mid_before.is_pure(),
        "pre-closure: local importer mislabels `mid` as pure (the bug)"
    );

    let upgraded = propagate_shard_axiom_profiles(&mut constants, &exprs, &strings);

    // Both `mid` (1 hop) and `top` (2 hops) must now carry CHOICE.
    let mid_after = find_const(&constants, &strings, "mid").axiom_profile;
    let top_after = find_const(&constants, &strings, "top").axiom_profile;
    assert!(
        mid_after.has(AxiomProfile::CHOICE),
        "mid should gain CHOICE"
    );
    assert!(
        top_after.has(AxiomProfile::CHOICE),
        "top should gain CHOICE transitively (2 hops)"
    );
    assert!(!top_after.is_pure(), "top is no longer reported as pure");
    // The axiom itself + mid + top all changed or already had bits; at least
    // mid and top are genuine upgrades.
    assert!(upgraded >= 2, "at least mid and top should be upgraded");
}

#[test]
fn test_shard_closure_pure_chain_stays_pure() {
    // A chain with no axioms must remain pure after closure.
    let module = mock_module_ap(vec![
        mock_constant_ap("Nat", ConstantKind::Inductive, false),
        constant_with_deps_ap("base", ConstantKind::Definition, &["Nat"]),
        constant_with_deps_ap("derived", ConstantKind::Theorem, &["base"]),
    ]);
    let (mut constants, exprs, strings) = lower_to_shard_parts(&module);
    let upgraded = propagate_shard_axiom_profiles(&mut constants, &exprs, &strings);
    assert_eq!(upgraded, 0, "no constant should gain axiom bits");
    assert!(find_const(&constants, &strings, "derived")
        .axiom_profile
        .is_pure());
}

#[test]
fn test_shard_closure_handles_dependency_cycle() {
    // Mutually recursive `a <-> b`, with `a` also depending on an axiom.
    // A naive recursive DFS would not terminate; the bitset fixed-point must.
    let module = mock_module_ap(vec![
        mock_constant_ap("propext", ConstantKind::Axiom, false),
        constant_with_deps_ap("a", ConstantKind::Definition, &["b", "propext"]),
        constant_with_deps_ap("b", ConstantKind::Definition, &["a"]),
    ]);
    let (mut constants, exprs, strings) = lower_to_shard_parts(&module);
    let _ = propagate_shard_axiom_profiles(&mut constants, &exprs, &strings);
    // Both halves of the cycle must end up carrying PROP_EXT.
    assert!(find_const(&constants, &strings, "a")
        .axiom_profile
        .has(AxiomProfile::PROP_EXT));
    assert!(
        find_const(&constants, &strings, "b")
            .axiom_profile
            .has(AxiomProfile::PROP_EXT),
        "cycle partner must also inherit the axiom"
    );
}

#[test]
fn test_shard_closure_empty_is_noop() {
    let mut constants: Vec<crate::types::MathverseConstantHeader> = Vec::new();
    let exprs: Vec<clean_kernel::flat::FlatExpr> = Vec::new();
    let strings: Vec<String> = Vec::new();
    assert_eq!(
        propagate_shard_axiom_profiles(&mut constants, &exprs, &strings),
        0
    );
}

#[test]
fn test_finalize_axiom_profiles_through_writer_end_to_end() {
    // End-to-end: the public `ShardWriter::finalize_axiom_profiles` (wired into
    // every conversion entry point) must close the chain in the written shard.
    let module = mock_module_ap(vec![
        mock_constant_ap("Classical.choice", ConstantKind::Axiom, false),
        constant_with_deps_ap(
            "uses_choice",
            ConstantKind::Definition,
            &["Classical.choice"],
        ),
        constant_with_deps_ap("thm", ConstantKind::Theorem, &["uses_choice"]),
    ]);
    let mut writer = crate::shard::ShardWriter::new();
    crate::lean4::olean::alpha::import_module(&module, &mut writer).expect("import should succeed");

    let upgraded = writer.finalize_axiom_profiles();
    assert!(upgraded >= 2, "uses_choice and thm should be upgraded");

    let mut buf = Vec::new();
    writer.write(&mut buf).expect("write should succeed");
    let reader = crate::shard::ShardReader::from_bytes(&buf).expect("read should succeed");

    let thm = find_const(&reader.constants, &reader.strings, "thm");
    assert!(
        thm.axiom_profile.has(AxiomProfile::CHOICE),
        "written shard header for `thm` must reflect transitive CHOICE"
    );
    assert!(!thm.axiom_profile.is_kernel_verified());
}

// ---------------------------------------------------------------------------
// Cross-shard (library-level) transitive closure tests
//
// These exercise `propagate_cross_shard_axiom_profiles`, which closes axiom
// profiles across shard boundaries after a library has been split at
// `shard_size_limit`. The within-shard pass (`finalize_axiom_profiles`) skips a
// dependency whose defining constant lives in a *different* shard, so a theorem
// in shard B that uses `Classical.choice` only through a constant defined in
// shard A is left looking pure. The regression assertions below pin exactly that
// pre-closure state, then prove the cross-shard pass repairs it.
// ---------------------------------------------------------------------------

/// Lower a module into a fresh `ShardWriter` and run the within-shard closure,
/// mirroring how the library builder seals each shard before the cross-shard
/// pass. Returns the sealed writer.
fn lower_to_sealed_writer(module: &ParsedModule) -> crate::shard::ShardWriter {
    let mut writer = crate::shard::ShardWriter::new();
    crate::lean4::olean::alpha::import_module(module, &mut writer).expect("import should succeed");
    writer.finalize_axiom_profiles();
    writer
}

/// Read a single constant's profile back from a writer by round-tripping it
/// through the binary shard format (the same bytes that hit disk).
fn writer_profile(writer: &crate::shard::ShardWriter, name: &str) -> AxiomProfile {
    let mut buf = Vec::new();
    writer.write(&mut buf).expect("write should succeed");
    let reader = crate::shard::ShardReader::from_bytes(&buf).expect("read should succeed");
    find_const(&reader.constants, &reader.strings, name).axiom_profile
}

#[test]
fn test_cross_shard_closure_captures_choice_across_shard_boundary() {
    // Shard A defines the axiom `Classical.choice` and a definition `taint`
    // that uses it. Shard B defines a theorem `top` that depends on `taint`
    // *by name* — exactly the cross-shard dependency the within-shard pass
    // cannot resolve (its `name_idx` is not in shard B's string table).
    let module_a = mock_module_ap(vec![
        mock_constant_ap("Classical.choice", ConstantKind::Axiom, false),
        constant_with_deps_ap("taint", ConstantKind::Definition, &["Classical.choice"]),
    ]);
    let module_b = mock_module_ap(vec![constant_with_deps_ap(
        "top",
        ConstantKind::Theorem,
        &["taint"],
    )]);

    let shard_a = lower_to_sealed_writer(&module_a);
    let shard_b = lower_to_sealed_writer(&module_b);

    // REGRESSION: within-shard closure leaves `top` reported pure, because
    // `taint` is in a *different* shard. This is the cross-shard soundness gap.
    let top_before = writer_profile(&shard_b, "top");
    assert!(
        top_before.is_pure(),
        "pre-cross-shard: `top` is mislabeled pure because its dep `taint` lives \
         in another shard (the gap)"
    );
    // Sanity: within shard A, `taint` already carries CHOICE (in-shard closure).
    assert!(
        writer_profile(&shard_a, "taint").has(AxiomProfile::CHOICE),
        "in-shard closure should already taint `taint` within shard A"
    );

    // Run the cross-shard closure over both shards (contiguous slice).
    let mut shards = vec![shard_a, shard_b];
    let upgraded = propagate_cross_shard_axiom_profiles(&mut shards);

    // `top` (in shard B, index 1) must now carry CHOICE, sourced transitively
    // through a dependency defined in shard A.
    let top_after = writer_profile(&shards[1], "top");
    assert!(
        top_after.has(AxiomProfile::CHOICE),
        "post-cross-shard: `top` must carry CHOICE through its cross-shard dep `taint`"
    );
    assert!(
        !top_after.is_pure(),
        "post-cross-shard: `top` is no longer reported as pure"
    );
    assert!(
        upgraded >= 1,
        "at least `top` should be upgraded by the cross-shard pass"
    );
}

#[test]
fn test_cross_shard_closure_pure_library_stays_pure() {
    // No axioms anywhere across two shards: nothing should be upgraded and the
    // cross-shard theorem must stay pure.
    let module_a = mock_module_ap(vec![
        mock_constant_ap("Nat", ConstantKind::Inductive, false),
        constant_with_deps_ap("base", ConstantKind::Definition, &["Nat"]),
    ]);
    let module_b = mock_module_ap(vec![constant_with_deps_ap(
        "derived",
        ConstantKind::Theorem,
        &["base"],
    )]);

    let mut shards = vec![
        lower_to_sealed_writer(&module_a),
        lower_to_sealed_writer(&module_b),
    ];
    let upgraded = propagate_cross_shard_axiom_profiles(&mut shards);
    assert_eq!(upgraded, 0, "a pure library should upgrade nothing");
    assert!(
        writer_profile(&shards[1], "derived").is_pure(),
        "cross-shard `derived` must remain pure"
    );
}

#[test]
fn test_cross_shard_closure_handles_cycle_across_shards() {
    // Cross-shard mutual dependency a (shard A) <-> b (shard B), with `a` also
    // depending on `propext`. A recursive walk that crosses shard boundaries
    // could loop forever; the global bitset fixed-point must terminate and
    // taint both halves.
    let module_a = mock_module_ap(vec![
        mock_constant_ap("propext", ConstantKind::Axiom, false),
        constant_with_deps_ap("a", ConstantKind::Definition, &["b", "propext"]),
    ]);
    let module_b = mock_module_ap(vec![constant_with_deps_ap(
        "b",
        ConstantKind::Definition,
        &["a"],
    )]);

    let mut shards = vec![
        lower_to_sealed_writer(&module_a),
        lower_to_sealed_writer(&module_b),
    ];
    let _ = propagate_cross_shard_axiom_profiles(&mut shards);
    assert!(
        writer_profile(&shards[0], "a").has(AxiomProfile::PROP_EXT),
        "`a` must carry PROP_EXT"
    );
    assert!(
        writer_profile(&shards[1], "b").has(AxiomProfile::PROP_EXT),
        "cross-shard cycle partner `b` must also inherit PROP_EXT"
    );
}

#[test]
fn test_cross_shard_closure_empty_is_noop() {
    let mut shards: Vec<crate::shard::ShardWriter> = Vec::new();
    assert_eq!(propagate_cross_shard_axiom_profiles(&mut shards), 0);
}
