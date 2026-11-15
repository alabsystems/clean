// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The meter's own charges: what each walk pays, and the equality mutant.

use super::stats::take;
use super::*;
use crate::expr::Expr;
use crate::name::Name;

/// `f (f (... (f x)))`, `links` deep, every node a fresh allocation.
fn chain(links: usize) -> Expr {
    let mut term = Expr::const_(Name::from_string("x"), vec![]);
    for _ in 0..links {
        term = Expr::app(Expr::const_(Name::from_string("f"), vec![]), term);
    }
    term
}

#[test]
fn equality_of_distinct_equal_allocations_charges_every_entered_pair() {
    let (left, right) = (chain(1_000), chain(1_000));
    let _ = take();
    let before = charged();
    assert!(left == right);
    let units = charged().wrapping_sub(before);
    // Each link enters its App pair and its `f` pair; the base enters `x`.
    assert_eq!(units, 2 * 1_000 + 1);
    let stats = take();
    assert_eq!(stats.equality_walks, 1);
    assert_eq!(stats.equality_visits, units);
    assert_eq!(stats.collided_walks, 0);
}

#[test]
fn equality_refused_by_root_metadata_charges_nothing() {
    let (left, right) = (chain(1_000), chain(999));
    let before = charged();
    assert!(left != right);
    assert_eq!(charged(), before, "an O(1) metadata refusal enters no pair");
}

#[test]
fn equality_shared_children_are_not_re_entered() {
    let left = chain(1_000);
    let right = Expr::app(Expr::const_(Name::from_string("g"), vec![]), left.clone());
    let left = Expr::app(Expr::const_(Name::from_string("g"), vec![]), left);
    let before = charged();
    assert!(left == right);
    // The roots, the two `g` constants and the two argument wrappers; below
    // them the argument's children are the same Arcs and are not entered.
    assert_eq!(charged().wrapping_sub(before), 3);
}

#[test]
fn equality_mutant_drops_exactly_the_equality_charge() {
    let (left, right) = (chain(1_000), chain(1_000));
    let before = charged();
    let equal = mutant::with_equality_charge_dropped(|| left == right);
    assert!(equal, "the mutant changes accounting, never the answer");
    assert_eq!(charged(), before, "MUTANT: the walk spent no budget");
    // The flag is restored on exit.
    assert!(left == right);
    assert_eq!(charged().wrapping_sub(before), 2 * 1_000 + 1);
}

#[test]
fn walk_charges_are_attributed_to_their_walk() {
    let _ = take();
    let before = charged();
    charge(Walk::Fold, 3);
    charge(Walk::Equiv, 5);
    charge(Walk::Probe, 7);
    assert_eq!(charged().wrapping_sub(before), 15);
    let stats = take();
    assert_eq!(
        (stats.fold_nodes, stats.equiv_nodes, stats.probes),
        (3, 5, 7)
    );
}

#[test]
fn instantiate_charges_the_nodes_it_descends_into() {
    // `fun _ => f (f ... (f #0))`: instantiating the body visits every link,
    // because each one carries the loose bound variable.
    let mut body = Expr::bvar(0);
    for _ in 0..100 {
        body = Expr::app(Expr::const_(Name::from_string("f"), vec![]), body);
    }
    let _ = take();
    let _ = body.instantiate(&Expr::const_(Name::from_string("x"), vec![]));
    let folded = take().fold_nodes;
    assert!(folded >= 100, "fold nodes {folded}");
}
