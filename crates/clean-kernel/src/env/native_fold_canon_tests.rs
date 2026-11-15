// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pins for the table's ROLE column (`native_fold_canon.rs`): a row must say
//! what it vouches for, no closure is pinned with two roles, and the reducer
//! fix the review forced (`UInt*.decEq`'s `isTrue` witness).

use std::collections::{HashMap, HashSet};

use super::*;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn lit(v: u64) -> Expr {
    Expr::nat_lit(v)
}

/// A row must say what it vouches for: a row without the role column, or
/// with an unknown role, is dropped (it can only REMOVE an admission).
#[test]
fn test_rows_without_a_role_are_dropped() {
    const HEX: &str = "ecbf39835eafba8bfdb5ef79a409a040dafa98560a8a7f3a83b4168c00ff526c";
    let text: &'static str = Box::leak(
        format!(
            "w\tNat.add\t{HEX}\n\
             w\tNat.add\t{HEX}\tfold\n\
             w\tNat.add\t{HEX}\tdefinition\n\
             w\tNat.add\t{HEX}\trefused\n\
             w\tNat.add\t{HEX}\treviewed\n\
             w\tNat.add\t{HEX}\tfold\textra\n"
        )
        .into_boxed_str(),
    );
    let roles: Vec<FoldRole> = parse_rows(text).map(|(_, _, _, role)| role).collect();
    assert_eq!(
        roles,
        vec![FoldRole::Fold, FoldRole::Definition, FoldRole::Refused]
    );
}

/// `UInt*.decEq`'s `isTrue` witness is `@Decidable.isTrue (a = a) (Eq.refl a)`.
/// It used to be `Decidable.isTrue (Eq.refl a)` — the proof in the
/// proposition slot, a term whose type is a `Pi` — which the review refused on
/// every equal pair (2026-09-28). Checked in Lean's reference theory at the
/// head application's own type.
#[test]
fn test_uint_dec_eq_true_witness_is_well_typed() {
    let env = Environment::with_prelude();
    for ty in ["UInt8", "UInt16", "UInt32", "UInt64"] {
        let head = n(&format!("{ty}.decEq"));
        let reducer = env.get_native_reducer(&head).expect("decEq reducer");
        let a = Expr::app(c(&format!("{ty}.ofNat")), lit(3));
        let b = Expr::app(c(&format!("{ty}.ofNat")), lit(3));
        let mut tc = TypeChecker::new(&env);
        tc.set_kernel_theory(crate::env::KernelTheory::LeanReference);
        let result = reducer(&[&a, &b]).expect("fires on equal operands");
        let term = Expr::apps(Expr::const_(head.clone(), vec![]), [a, b]);
        let head_ty = tc.infer_type(&term).expect("head application typed");
        let result_ty = tc.infer_type(&result).expect("witness typed");
        assert!(
            tc.is_def_eq(&head_ty, &result_ty),
            "{ty}.decEq 3 3: witness type {result_ty:?}, head type {head_ty:?}"
        );
    }
}

/// No digest is pinned both `fold` and `refused`: the kernel resolves such a
/// pair as `refused` (the veto), so a `fold` row beside it would claim a fold
/// that never fires. Each battery reads the other worlds' `refused` rows and
/// demotes its own `fold` row (`native_fold_review_roles.rs`); `fold` beside
/// `definition` is expected (a `definition` row records no evidence).
#[test]
fn test_no_digest_is_pinned_fold_and_refused() {
    let mut roles: HashMap<(String, String), HashSet<String>> = HashMap::new();
    for (world, name, hex, role) in canonical_fold_rows() {
        roles
            .entry((name, hex))
            .or_default()
            .insert(format!("{role}@{world}"));
    }
    let conflicts: Vec<_> = roles
        .iter()
        .filter(|(_, rs)| {
            let fold = rs.iter().any(|r| r.starts_with("fold@"));
            let refused = rs.iter().any(|r| r.starts_with("refused@"));
            fold && refused
        })
        .collect();
    assert!(
        conflicts.is_empty(),
        "digests pinned both `fold` and `refused`: {conflicts:#?}"
    );
}
