// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Test code by its own head: the source gates read a file-level #![cfg(test)]
// as proof (headed_cfg_test in scripts/check_add_decl_ratchet.py).
#![cfg(test)]

use super::*;
use clean_kernel::expr::BinderInfo;
use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_mathverse::library::MathverseLibrary;
use clean_mathverse::shard::{ShardReader, ShardWriter};
use clean_mathverse::trust::policy::TrustPolicy;
use clean_mathverse::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem,
};

/// Build a shard holding a single constant whose name has NO token overlap
/// with the goal's extracted symbols ("Nat"), but whose stored type is
/// structurally `Pi(Nat, Nat)`. If the discrimination tree is queried, the
/// constant is found via `MatchReason::TypeUnification`; otherwise BM25
/// and the symbol-overlap fallback both miss (the constant's tokens are
/// `zzz`, `qqq`, `unique`, `premise`, `xyz` — none match `Nat`).
fn build_type_only_shard() -> ShardReader {
    let mut writer = ShardWriter::new();

    // "Nat" is the goal's constant name. Intern it so the disc tree's
    // stored paths share a name_idx with the query expression built at
    // search time (via `MathverseLibrary::add_query_expr`).
    let nat_name_idx = writer.add_string("Nat");

    // Deliberately exotic constant name with zero token overlap with "Nat".
    let cst_name_idx = writer.add_string("zzz_qqq_unique_premise_xyz");

    let l0 = writer.add_level(FlatLevel::zero());
    let sort0 = writer.add_expr(FlatExpr::sort(l0));

    // Pi(Nat, Nat): two separate Nat const refs, bound under a Pi.
    let nat_a = writer.add_expr(FlatExpr::const_ref(nat_name_idx, u32::MAX));
    let nat_b = writer.add_expr(FlatExpr::const_ref(nat_name_idx, u32::MAX));
    let pi_nat_nat = writer.add_expr(FlatExpr::pi(0, nat_a, nat_b));

    writer.add_constant(MathverseConstantHeader {
        name_idx: cst_name_idx,
        type_idx: pi_nat_nat,
        value_idx: sort0,
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

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

/// RAII guard that clears the thread-local MathverseLibrary on drop so a
/// test leak cannot poison sibling tests on the same thread.
struct MathverseLibGuard;
impl Drop for MathverseLibGuard {
    fn drop(&mut self) {
        super::super::mathverse_use::clear_mathverse_library();
    }
}

#[test]
fn test_mathverse_suggest_uses_disc_tree_at_tactic_layer() {
    // Regression guard for #3412. Before the fix, `eval_mathverse_suggest`
    // passed `None` for `goal_type_idx`, making the discrimination tree
    // (60% of ranking weight by default) dead code. This test would fail
    // in the pre-fix behavior because no other channel can surface the
    // stored candidate:
    //   - goal symbols: ["Nat"]  -> BM25 against "zzz_qqq_unique_..." = 0
    //   - symbol overlap: tokens ["zzz","qqq","unique","premise","xyz"]
    //     vs ["Nat"] -> 0
    //   - dependency neighbors: empty (no context_names)
    let _guard = MathverseLibGuard;

    let shard = build_type_only_shard();
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    super::super::mathverse_use::set_mathverse_library(lib);

    // Goal: Pi(Nat, Nat). eval_mathverse_suggest only reads the goal for
    // search; it never closes. A kernel Expr is fine even though
    // Pi(Nat,Nat) is a type, not a Prop.
    let nat_a = Expr::const_str("Nat");
    let nat_b = Expr::const_str("Nat");
    let goal = Expr::pi(BinderInfo::Default, nat_a, nat_b);

    let env = Environment::new();
    let mut state = ProofState::new(env, goal);

    let result = eval_mathverse_suggest(&mut state, &[]);
    let err = result.expect_err("mathverse_suggest never closes the goal");
    match err {
        TacticError::SearchExhausted { tactic, detail } => {
            assert_eq!(tactic, "mathverse_suggest");
            assert!(
                detail.contains("showing") && detail.contains("candidate"),
                "disc tree must surface >=1 candidate; got detail: {detail}"
            );
            assert!(
                !detail.contains("no candidates found"),
                "disc tree wired -> must not report 'no candidates found': {detail}"
            );
        }
        other => panic!("expected SearchExhausted, got {other:?}"),
    }
}

#[test]
fn test_mathverse_suggest_returns_no_candidates_when_every_channel_misses() {
    // Negative control. Confirms the positive test above is attributable
    // to the disc tree and not a spurious "everything matches" bug.
    // Goal symbols are unknown strings absent from the shard's string
    // table, so the disc tree's name_idx lookups on the goal's Const
    // nodes miss all stored paths. The symbol-overlap fallback also
    // misses: none of the goal's tokens overlap with the shard constant's
    // exotic name.
    let _guard = MathverseLibGuard;

    let shard = build_type_only_shard();
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    super::super::mathverse_use::set_mathverse_library(lib);

    let a = Expr::const_str("UnknownSymA_qq");
    let b = Expr::const_str("UnknownSymB_qq");
    let goal = Expr::pi(BinderInfo::Default, a, b);

    let env = Environment::new();
    let mut state = ProofState::new(env, goal);

    let result = eval_mathverse_suggest(&mut state, &[]);
    let err = result.expect_err("mathverse_suggest never closes the goal");
    match err {
        TacticError::SearchExhausted { tactic, detail } => {
            assert_eq!(tactic, "mathverse_suggest");
            assert!(
                detail.contains("no candidates found"),
                "no channel should match; got detail: {detail}"
            );
        }
        other => panic!("expected SearchExhausted, got {other:?}"),
    }
}
