// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_auto::bridge::ay_contract::test_utils::residual_trust_summary_from_source;
use clean_auto::bridge::ay_contract::ResidualTrustSource;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};

#[test]
fn test_merge_proven_branch_preserves_meta_and_trust() {
    let env = Environment::with_prelude();
    let target = Expr::const_(Name::from_string("True"), vec![]);
    let mut parent = ProofState::new(env, target);
    let goal = parent.current_goal().expect("goal should exist").clone();
    let root_meta = parent.root_meta_id;
    let parent_next_fvar = parent.next_fvar;
    let mut focused = parent.clone_with_goal(goal);

    assert!(
        focused.metas.assign(
            root_meta,
            Expr::const_(Name::from_string("True.intro"), vec![])
        ),
        "focused branch should be able to assign the root meta"
    );
    focused.record_sorry();
    focused.next_fvar += 3;

    let branch_next_fvar = focused.next_fvar;
    let branch_ledger = focused.trust_ledger();
    let branch_metas = Box::new(focused.metas);

    merge_proven_branch(&mut parent, branch_metas, branch_ledger, branch_next_fvar);

    assert!(
        parent.metas.is_assigned(root_meta),
        "parent state must inherit the proven branch meta assignment"
    );
    assert_eq!(
        parent.trust_ledger().sorry_count,
        1,
        "parent trust ledger must inherit the proven branch trust entry"
    );
    assert_eq!(
        parent.trusted_axiom_count(),
        1,
        "legacy trusted_axiom_count should continue to reflect the merged ledger"
    );
    assert_eq!(
        parent.next_fvar, branch_next_fvar,
        "parent next_fvar must advance to the proven branch watermark"
    );
    assert!(
        parent.next_fvar > parent_next_fvar,
        "merge should preserve clone-allocated fvar progress"
    );
}

#[test]
fn test_merge_proven_branch_adopts_exact_ay_provenance() {
    let env = Environment::with_prelude();
    let target = Expr::const_(Name::from_string("True"), vec![]);
    let mut parent = ProofState::new(env, target);
    let goal = parent.current_goal().expect("goal should exist").clone();
    let mut focused = parent.clone_with_goal(goal);

    parent.record_trusted_ay_residual(
        1,
        residual_trust_summary_from_source(ResidualTrustSource::AletheTrustStep),
    );
    focused.record_trusted_ay_residual(
        1,
        residual_trust_summary_from_source(ResidualTrustSource::LocalReconstructionGap),
    );

    let branch_next_fvar = focused.next_fvar;
    let branch_ledger = focused.trust_ledger();
    let branch_metas = Box::new(focused.metas);
    merge_proven_branch(&mut parent, branch_metas, branch_ledger, branch_next_fvar);

    let ledger = parent.trust_ledger();
    assert_eq!(ledger.trusted_ay_count, 1);
    assert_eq!(ledger.trusted_ay_provenance.alethe_trust_steps, 0);
    assert_eq!(ledger.trusted_ay_provenance.local_gap_steps, 1);
    assert_eq!(ledger.trusted_ay_provenance.unclassified_steps, 0);
}
