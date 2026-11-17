// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Test code by its own head: the source gates read a file-level #![cfg(test)]
// as proof (headed_cfg_test in scripts/check_add_decl_ratchet.py).
#![cfg(test)]

use super::*;
use clean_kernel::{BinderInfo, Declaration, Name};
use clean_mathverse::export::kernel_export::KernelShardBuilder;
use clean_mathverse::library::MathverseLibrary;
use clean_mathverse::premise_select::{search_for_kernel_goal, PremiseConfig};
use clean_mathverse::shard::ShardReader;
use clean_mathverse::shard_verify::verify_native_shard;
use clean_mathverse::trust::policy::TrustPolicy;

struct MathverseLibGuard;
impl Drop for MathverseLibGuard {
    fn drop(&mut self) {
        super::super::mathverse_use::clear_mathverse_library();
    }
}

fn native_replay_dependency() -> Declaration {
    Declaration::Theorem {
        name: Name::from_string("MathverseReplayGate.dep"),
        level_params: vec![],
        type_: Expr::const_str("True"),
        value: Expr::const_str("True.intro"),
    }
}

fn native_replay_candidate() -> Declaration {
    let true_prop = Expr::const_str("True");
    let goal_type = Expr::apps(
        Expr::const_str("Iff"),
        [true_prop.clone(), true_prop.clone()],
    );
    let dep = Expr::const_str("MathverseReplayGate.dep");
    let forward = Expr::lam(BinderInfo::Default, true_prop.clone(), dep.clone());
    let backward = Expr::lam(BinderInfo::Default, true_prop.clone(), dep);

    Declaration::Theorem {
        name: Name::from_string("MathverseReplayGate.close_iff_true"),
        level_params: vec![],
        type_: goal_type,
        value: Expr::apps(
            Expr::const_str("Iff.intro"),
            [true_prop.clone(), true_prop, forward, backward],
        ),
    }
}

fn build_native_replay_library() -> MathverseLibrary {
    let mut builder = KernelShardBuilder::new();
    builder
        .add_declaration(&native_replay_dependency(), &["mathverse-replay-gate"])
        .expect("export native replay dependency");
    builder
        .add_declaration(&native_replay_candidate(), &["mathverse-replay-gate"])
        .expect("export native replay candidate");

    let tmp = tempfile::tempdir().expect("native replay tempdir");
    let shard_path = tmp.path().join("clean-native.mathverse");
    builder
        .write_to_file(&shard_path)
        .expect("write native replay shard");

    let report = verify_native_shard(&shard_path).expect("run native shard gate");
    assert_eq!(
        report.checked, 2,
        "native replay gate should check both declarations"
    );
    assert!(
        report.violations.is_empty(),
        "native replay shard should pass the strict native gate: {report:?}"
    );

    let bytes = std::fs::read(&shard_path).expect("read verified native replay shard");
    let shard = ShardReader::from_bytes(&bytes).expect("load verified native replay shard");
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard)
        .expect("load verified native replay shard into MathverseLibrary");
    lib
}

#[test]
fn test_strict_mathverse_use_search_verifies_loads_native_deps_and_closes_goal() {
    let _guard = MathverseLibGuard;
    let mut lib = build_native_replay_library();
    let true_prop = Expr::const_str("True");
    let target = Expr::apps(Expr::const_str("Iff"), [true_prop.clone(), true_prop]);

    let candidates = search_for_kernel_goal(
        &mut lib,
        &target,
        &[],
        &PremiseConfig {
            max_results: 3,
            ..PremiseConfig::default()
        },
    );
    assert!(
        candidates
            .iter()
            .any(|candidate| candidate.name == "MathverseReplayGate.close_iff_true"),
        "Mathverse search should produce the native replay candidate: {candidates:?}"
    );

    super::super::mathverse_use::set_mathverse_library(lib);
    let mut state = ProofState::new(Environment::with_prelude(), target);
    eval_mathverse_use(&mut state, &[])
        .expect("strict mathverse_use should close via native replay");

    assert!(
        state.is_complete(),
        "strict mathverse_use should close the goal after loading the native dependency"
    );
    assert!(
        state
            .env
            .get_const(&Name::from_string("MathverseReplayGate.dep"))
            .is_some(),
        "mathverse_use should load the native dependency into the proof environment"
    );
    assert!(
        state
            .env
            .get_const(&Name::from_string("MathverseReplayGate.close_iff_true"))
            .is_some(),
        "mathverse_use should load the selected native theorem into the proof environment"
    );
}
