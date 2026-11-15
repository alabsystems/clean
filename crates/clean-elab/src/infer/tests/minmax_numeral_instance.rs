// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `min` / `max` of bare numerals elaborate at `Nat`, as in Lean 4.8.0, with
//! the prelude's `Int.instMin` / `Int.instMax` registered after the `Nat`
//! instances at the same (Lean default) priority; an `Int`-annotated
//! numeral elaborates at `Int`.
//!
//! Pinned Lean 4.8.0 as oracle (2026-10-07, `set_option pp.all true`):
//! `#check max 3 5` is `@Max.max.{0} Nat Nat.instMax …`, `#check min 3 5` is
//! `@Min.min.{0} Nat instMinNat …` and `#check max (3 : Int) 5` is
//! `@Max.max.{0} Int Int.instMax …`. Every one of the four instances is
//! declared with no `(priority := …)` (`Init/Prelude.lean:1782`,
//! `Init/Data/Nat/Basic.lean:721`, `Init/Data/Int/Basic.lean:332,334`).
//! Clean names its `Max Nat` instance `instMaxNat` (`env/order_ord.rs`).

use super::*;

fn elaborated_def(env: &mut Environment, source: &str) -> (Expr, Expr) {
    let decl = parse_decl_for_elab(source).unwrap_or_else(|e| panic!("{source}: {e}"));
    match crate::elaborate_decl_and_register(env, &decl) {
        Ok(ElabResult::Definition { ty, val, .. }) => (ty, val),
        other => panic!("{source}: expected a registered definition, got {other:?}"),
    }
}

/// Elaborate each `(source, instance, other)` and require the definition's
/// type to be `carrier` and its value to name `instance` and not `other`.
fn assert_minmax_at(carrier: &str, cases: [(&str, &str, &str); 2]) {
    let mut env = Environment::with_prelude();
    let carrier_ty = Expr::const_(Name::from_string(carrier), vec![]);
    for (source, instance, other) in cases {
        let (ty, val) = elaborated_def(&mut env, source);
        assert_eq!(ty, carrier_ty, "{source}: Lean 4.8 elaborates at {carrier}");
        let constants = val.collect_constants();
        assert!(
            constants.contains(&Name::from_string(instance)),
            "{source}: expected `{instance}`, got {constants:?}"
        );
        assert!(
            !constants.contains(&Name::from_string(other)),
            "{source}: `{other}` was selected: {constants:?}"
        );
    }
}

#[test]
fn test_minmax_bare_numerals_elaborate_at_nat_not_int() {
    assert_minmax_at(
        "Nat",
        [
            ("def max_numerals := max 3 5", "instMaxNat", "Int.instMax"),
            ("def min_numerals := min 3 5", "instMinNat", "Int.instMin"),
        ],
    );
}

#[test]
fn test_minmax_int_annotated_numerals_elaborate_at_int() {
    assert_minmax_at(
        "Int",
        [
            (
                "def max_int := max (3 : Int) 5",
                "Int.instMax",
                "instMaxNat",
            ),
            (
                "def min_int := min (3 : Int) 5",
                "Int.instMin",
                "instMinNat",
            ),
        ],
    );
}
