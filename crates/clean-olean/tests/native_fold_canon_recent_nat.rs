// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Review the two Nat folds needed by the genuine recent UInt witness.
//! The ordinary genuine UInt.Basic load never uses a fold-authority bypass.
//! Re-pin uses the existing test-only reference review, then deliberately
//! fails: only a fresh ordinary run measures production authority.

use clean_kernel::env::{
    canonical_fold_rows, native_fold_mint_bypass, native_fold_review, Environment,
};
use clean_kernel::{LeanWorld, Name};
use std::collections::BTreeSet;
use std::path::Path;

#[path = "support/fold_canon.rs"]
mod fold_canon;
use fold_canon::{check_world, fold_with_required_definitions, mint, repin_requested};

const REVIEWED: [&str; 2] = ["Nat.mod", "Nat.xor"];

fn check_recent(world: LeanWorld) {
    let repin = repin_requested();
    if repin {
        // The existing review bootstrap is process-global. Keep the genuine
        // load of the other world outside that scope too.
        assert!(
            std::env::args().any(|arg| arg == "--test-threads=1"),
            "canonical regeneration requires --test-threads=1"
        );
    }
    let decision = clean_olean::source_world_for_file(Path::new("RecentNat.lean"), Some(world))
        .expect("the exact measured recent world and installed library are required");
    let mut env = Environment::for_lean_replay();
    clean_olean::declare_environment_world(&mut env, world.tag()).unwrap();
    let Ok(clean_olean::ImportWorld::Explicit { lib, .. }) = decision.imports() else {
        panic!("canonical review requires the exact explicit library")
    };
    clean_olean::load_module_with_deps(&mut env, "Init.Data.UInt.Basic", std::slice::from_ref(lib))
        .expect("ordinary genuine UInt.Basic load must succeed without an authority bypass");
    assert_eq!(clean_olean::environment_world(&env), Some(world.tag()));
    assert_eq!(
        env.get_inductive(&Name::from_string("Decidable"))
            .unwrap()
            .constructor_names,
        vec![Name::from_string("Decidable.intro")]
    );

    let label = format!("lean-{}", world.tag());
    let minted = mint(&label, &env);
    let reviewed: Vec<_> = minted
        .iter()
        .filter(|(_, name, _)| REVIEWED.contains(&name.as_str()))
        .cloned()
        .collect();
    assert_eq!(reviewed.len(), REVIEWED.len());
    for (_, name, digest) in &reviewed {
        assert!(
            !canonical_fold_rows()
                .iter()
                .any(|(_, old_name, old_digest, role)| old_name == name
                    && old_digest == digest
                    && role == "refused"),
            "an existing refused-role veto remains binding for {name}/{digest}"
        );
        let check = || native_fold_review::review(&env, &Name::from_string(name), !repin);
        // As in the existing canonical batteries, a first reference review
        // must exercise the fold before its digest is in the compiled table.
        // Only this test-only reference review uses the bootstrap; the
        // genuine load above and every ordinary production leg do not.
        let review = if repin {
            native_fold_mint_bypass::run(check)
        } else {
            check()
        };
        eprintln!("RECENT_NAT_REVIEW {label} {name}: {review:#?}");
        // The existing shared review uses every pair of its thirteen Nat
        // boundary inputs, including zero and values beyond u64. Keep its
        // type/independent/definition/kernel legs and normal production leg.
        assert_eq!(review.cases, 169);
        assert_eq!(review.fired, 169);
        assert_eq!(review.unanswered, 0);
        assert!(review.passed(), "{label} {name}: {review:#?}");
    }

    // Include the complete transitive boundary closure deterministically,
    // even when another world already knows the same bytes. Otherwise two
    // recent worlds sharing a digest could each depend on the other's row
    // and disappear from both batteries on the next ordinary run.
    let required_arguments: BTreeSet<String> = REVIEWED
        .iter()
        .flat_map(|name| native_fold_review::recognized_arguments(&env, &Name::from_string(name)))
        .filter(|name| env.get_const(name).is_some())
        .map(ToString::to_string)
        .collect();
    assert!(
        required_arguments
            .iter()
            .all(|name| minted.iter().any(|(_, minted_name, _)| minted_name == name)),
        "every present required argument must have a measured definition closure"
    );
    let rows = fold_with_required_definitions(
        &env,
        &reviewed,
        &required_arguments.into_iter().collect::<Vec<_>>(),
        &minted,
    );
    let folded: BTreeSet<_> = rows
        .iter()
        .filter(|(_, _, _, role)| role == "fold")
        .map(|(_, name, _, _)| name.as_str())
        .collect();
    assert_eq!(folded, BTreeSet::from(REVIEWED));
    assert!(rows
        .iter()
        .all(|(_, _, _, role)| role == "fold" || role == "definition"));
    for row in &rows {
        eprintln!("RECENT_NAT_ROW\t{}\t{}\t{}\t{}", row.0, row.1, row.2, row.3);
    }
    check_world(&label, &rows);
    assert!(
        !repin_requested(),
        "{label}: reviewed rows written; rebuild and run without CLEAN_NATIVE_FOLD_REPIN before any production claim"
    );
    for name in REVIEWED {
        assert!(env.native_fold_authorized(&Name::from_string(name)));
        native_fold_review::fold_row_fires(&env, &Name::from_string(name))
            .unwrap_or_else(|error| panic!("{label} {name}: {error}"));
    }
}

#[test]
fn genuine_435_nat_mod_xor_folds_are_reviewed_and_pinned() {
    check_recent(LeanWorld::Lean435);
}

#[test]
fn genuine_436rc2_nat_mod_xor_folds_are_reviewed_and_pinned() {
    check_recent(LeanWorld::Lean436Rc2);
}
