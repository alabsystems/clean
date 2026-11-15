// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! G76 (ledger class (146)), continued from `match_catch_all_sharing.rs`: the
//! named catch-all's context (a false acceptance closed with the sharing) and
//! the shape of trust-ir `Pred.impliesFuel`, through the elaborator's
//! production entry. Every value is the pinned Lean 4.8.0 binary's (checked
//! 2026-10-16; repro row G76 under `reports/trust-ir-semantics-probe/repros/`
//! is the same `Pred` shape).

use super::match_catch_all_sharing::{refused, register_ok, registers_within};
use super::*;
use std::time::Duration;

/// A named catch-all's right-hand side sees the match's context and its own
/// binder — never the covered constructor's fields, which Lean's alternative
/// `fun x => rhs` does not bind. Pinned Lean 4.8.0's `assumption` here finds
/// `k`, so `f (some 5) 7 = 7`; Clean's per-constructor elaboration had the
/// `some` field (`5`) in scope, picked it, and certified `f (some 5) 7 = 5`,
/// which Lean refuses — a false acceptance.
#[test]
fn test_match_named_catch_all_rhs_does_not_see_constructor_fields() {
    let mut env = Environment::with_prelude();
    register_ok(
        &mut env,
        "def f (o : Option Nat) (k : Nat) : Nat :=\n  match o with\n  | none => 0\n  | x => by assumption",
    );
    register_ok(&mut env, "theorem f_some : f (some 5) 7 = 7 := rfl");
    register_ok(&mut env, "theorem f_none : f none 7 = 0 := rfl");
    refused(
        &mut env,
        "f_field",
        "theorem f_field : f (some 5) 7 = 5 := rfl",
    );
}

/// The shape of trust-ir `Pred.impliesFuel`, reduced: a multi-discriminant
/// match with catch-all rows whose last row's right-hand side nests five
/// catch-all matches, recursing on fuel through `List.any` / `List.all`.
const MINI_PRED: &str = "inductive P where
  | atom : Nat → P
  | iv : Int → Int → P
  | nz : P
  | conj : List P → P
  | disj : List P → P
  | top : P
  | bot : P";

const MINI_PRED_SAME: &str = "def P.same : P → P → Bool
  | .atom a, .atom b => a == b
  | .iv a b, .iv c d => a == c && b == d
  | .nz, .nz => true
  | .top, .top => true
  | .bot, .bot => true
  | _, _ => false";

const MINI_PRED_IMPLIES: &str = "def P.impliesFuel : Nat → P → P → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    match a, b with
    | .bot, _ => true
    | _, .bot => false
    | _, .top => true
    | .top, _ => false
    | a, b =>
      if P.same a b then true
      else if (match a with
               | .conj cs => cs.any (fun c => P.impliesFuel fuel c b)
               | _ => false) then true
      else if (match b with
               | .disj cs => cs.any (fun c => P.impliesFuel fuel a c)
               | _ => false) then true
      else
        match b with
        | .conj cs => cs.all (fun c => P.impliesFuel fuel a c)
        | _ =>
          match a with
          | .disj cs => cs.all (fun c => P.impliesFuel fuel c b)
          | _ =>
            match b with
            | .iv lo hi =>
              match a with
              | .iv alo ahi => decide (lo ≤ alo) && decide (ahi ≤ hi)
              | _ => false
            | .nz =>
              match a with
              | .iv lo hi => decide (0 < lo) || decide (hi < 0)
              | _ => false
            | .atom _ => false
            | .top => false
            | .bot => false
            | .conj _ => false
            | .disj _ => false";

/// `(name, fuel a b, value)` — pinned Lean 4.8.0's values.
const MINI_PRED_CASES: &[(&str, &str, &str)] = &[
    ("p_iv_in", "5 (.iv 2 3) (.iv 0 5)", "true"),
    ("p_iv_out", "5 (.iv 0 5) (.iv 2 3)", "false"),
    ("p_conj_nz", "5 (.conj [.top, .iv 1 2]) .nz", "true"),
    ("p_disj_r", "5 (.iv 1 2) (.disj [.atom 3, .iv 0 4])", "true"),
    ("p_disj_l", "5 (.disj [.iv 1 2, .iv 3 4]) (.iv 0 9)", "true"),
    ("p_top_l", "5 .top (.iv 0 1)", "false"),
    ("p_fuel0", "0 .bot .bot", "false"),
    ("p_conj_r", "3 (.atom 3) (.conj [.atom 3, .top])", "true"),
    ("p_neg_nz", "3 (.iv (-2) (-1)) .nz", "true"),
    ("p_zero_nz", "3 (.iv (-2) 1) .nz", "false"),
    ("p_fuel1", "1 (.conj [.iv 1 2]) (.iv 0 3)", "false"),
    ("p_fuel2", "2 (.conj [.iv 1 2]) (.iv 0 3)", "true"),
];

#[test]
fn test_match_pred_implies_shape_computes_lean_values() {
    let mut decls = vec![
        MINI_PRED.to_string(),
        MINI_PRED_SAME.to_string(),
        MINI_PRED_IMPLIES.to_string(),
    ];
    for (name, args, value) in MINI_PRED_CASES {
        decls.push(format!(
            "theorem {name} : P.impliesFuel {args} = {value} := rfl"
        ));
    }
    decls.push(
        "theorem p_dec : P.impliesFuel 5 (.iv 2 3) (.iv 0 5) = true := by decide".to_string(),
    );
    let size = match registers_within(decls, "P.impliesFuel", Duration::from_secs(300)) {
        Ok(size) => size,
        Err(err) => panic!("{err}"),
    };
    assert!(
        size.tree < 20_000,
        "`P.impliesFuel` has a tree of {} nodes",
        size.tree
    );
}

#[test]
fn test_match_pred_implies_shape_false_values_refused() {
    let mut env = Environment::with_prelude();
    for src in [MINI_PRED, MINI_PRED_SAME, MINI_PRED_IMPLIES] {
        register_ok(&mut env, src);
    }
    refused(
        &mut env,
        "p_false_iv",
        "theorem p_false_iv : P.impliesFuel 5 (.iv 0 5) (.iv 2 3) = true := rfl",
    );
    refused(
        &mut env,
        "p_false_fuel",
        "theorem p_false_fuel : P.impliesFuel 1 (.conj [.iv 1 2]) (.iv 0 3) = true := rfl",
    );
    refused(
        &mut env,
        "p_false_top",
        "theorem p_false_top : P.impliesFuel 5 .top (.iv 0 1) = true := by decide",
    );
}
