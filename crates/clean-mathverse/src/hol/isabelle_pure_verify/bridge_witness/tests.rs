// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Witness-sourcing tests: a real on-disk `.mathverse` shard is read back through
//! the production `shard_dir_facts` path and its named witness loaded (type +
//! value) into a replay env, gated foundationally by the kernel.

use std::collections::BTreeSet;
use std::path::Path;

use clean_kernel::env::is_foundational_axiom;
use clean_kernel::{Environment, Expr, Name};

use super::{load_bridge_witnesses, WitnessLoadStats};
use crate::hol::opentheory_shard::lower_kernel_expr;
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

/// A replay env carrying the base inductives the Mathlib witnesses reference.
fn base_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_iff().expect("init_iff");
    env.init_or().expect("init_or");
    // `Classical.em` + `Or` + `False` + `False.elim` — the foundational witness
    // base the Isabelle→Mathlib logical alias rows discharge against.
    env.init_classical().expect("init_classical");
    env
}

fn classical_em_type(env: &Environment) -> Expr {
    env.get_const(&Name::from_string("Classical.em"))
        .expect("Classical.em resident after init_classical")
        .type_
        .clone()
}

/// Write a single-constant `.mathverse` shard `<name>.mathverse` into `dir` with
/// the given type/value and KV verdict — the exact bytes the Mathlib import lane
/// (`clean mathverse stamp-verified`) emits for one constant.
fn write_witness_shard(dir: &Path, name: &str, type_: &Expr, value: Option<&Expr>, kv: bool) {
    let mut w = ShardWriter::new();
    let name_idx = w.add_string(name);
    let type_idx = lower_kernel_expr(type_, &mut w);
    let value_idx = match value {
        Some(v) => lower_kernel_expr(v, &mut w),
        None => NO_VALUE,
    };
    let import_confidence = if kv {
        ImportConfidence::KernelVerified
    } else {
        ImportConfidence::Translated
    } as u8;
    w.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence,
        content_domain: ContentDomain::Logic as u8,
        decl_kind: DeclKind::Theorem as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    let mut buf = Vec::new();
    w.write(&mut buf).expect("serialize witness shard");
    std::fs::write(dir.join(format!("{name}.mathverse")), &buf).expect("write witness shard file");
}

fn wanted(names: &[&str]) -> BTreeSet<String> {
    names.iter().map(|s| (*s).to_string()).collect()
}

/// The flagship: a KV-stamped `em := Classical.em` shard loads into the replay
/// env as a value-bearing witness with a foundational-only closure — read back
/// through the real `.mathverse` file, not hand-injected.
#[test]
fn test_load_em_witness_from_real_kv_shard_foundational() {
    let mut env = base_env();
    let em_ty = classical_em_type(&env);
    let dir = tempfile::tempdir().expect("tempdir");
    write_witness_shard(
        dir.path(),
        "em",
        &em_ty,
        Some(&Expr::const_str("Classical.em")),
        true,
    );

    let stats = load_bridge_witnesses(&mut env, dir.path(), &wanted(&["em"]));
    assert_eq!(stats.requested, 1);
    assert_eq!(stats.present, 1);
    assert_eq!(stats.candidates, 1);
    assert_eq!(stats.loaded, 1, "em must load: {stats:?}");

    let em = Name::from_string("em");
    assert!(env.get_const(&em).is_some(), "em resident after load");
    let deps = env.axiom_deps(&em).expect("em closure");
    assert!(
        deps.iter().all(is_foundational_axiom),
        "em closure must be foundational: {deps:?}"
    );
}

/// A witness present in the shard but NOT stamped `KernelVerified` is never
/// loaded — the shard's word alone cannot mint a usable witness.
#[test]
fn test_non_kv_witness_is_skipped() {
    let mut env = base_env();
    let em_ty = classical_em_type(&env);
    let dir = tempfile::tempdir().expect("tempdir");
    write_witness_shard(
        dir.path(),
        "em",
        &em_ty,
        Some(&Expr::const_str("Classical.em")),
        false, // NOT KernelVerified
    );

    let stats = load_bridge_witnesses(&mut env, dir.path(), &wanted(&["em"]));
    assert_eq!(stats.present, 1);
    assert_eq!(stats.skipped_not_kv, 1);
    assert_eq!(stats.loaded, 0);
    assert!(
        env.get_const(&Name::from_string("em")).is_none(),
        "a non-KV witness must not enter the env"
    );
}

/// A witness whose value the kernel rejects (its type does not match its value)
/// is declined on `add_decl`, not trusted — the kernel is the gate.
#[test]
fn test_kernel_rejected_witness_is_skipped() {
    let mut env = base_env();
    // Type claims `Prop` (`Sort 0`) but the value is `Classical.em` (a ∀-proof) —
    // a deliberate type/value mismatch the kernel must reject.
    let bogus_ty = Expr::prop();
    let dir = tempfile::tempdir().expect("tempdir");
    write_witness_shard(
        dir.path(),
        "bogus",
        &bogus_ty,
        Some(&Expr::const_str("Classical.em")),
        true,
    );

    let stats = load_bridge_witnesses(&mut env, dir.path(), &wanted(&["bogus"]));
    assert_eq!(stats.present, 1);
    assert_eq!(stats.candidates, 1);
    assert_eq!(stats.skipped_kernel_reject, 1);
    assert_eq!(stats.loaded, 0);
    assert!(env.get_const(&Name::from_string("bogus")).is_none());
}

/// Names outside the wanted set are ignored, and an empty/unreadable directory is
/// inert (no env mutation) — the OFF-invariance floor.
#[test]
fn test_unwanted_names_ignored_and_empty_dir_inert() {
    let mut env = base_env();
    let em_ty = classical_em_type(&env);
    let dir = tempfile::tempdir().expect("tempdir");
    write_witness_shard(
        dir.path(),
        "em",
        &em_ty,
        Some(&Expr::const_str("Classical.em")),
        true,
    );

    // Wanting a different name leaves `em` untouched.
    let stats = load_bridge_witnesses(&mut env, dir.path(), &wanted(&["not_and_or"]));
    assert_eq!(stats.requested, 1);
    assert_eq!(stats.present, 0);
    assert_eq!(stats.loaded, 0);
    assert!(env.get_const(&Name::from_string("em")).is_none());

    // A nonexistent directory is inert.
    let empty = tempfile::tempdir().expect("tempdir2");
    let stats2 = load_bridge_witnesses(&mut env, empty.path(), &wanted(&["em"]));
    assert_eq!(
        stats2,
        WitnessLoadStats {
            requested: 1,
            ..Default::default()
        }
    );
}
