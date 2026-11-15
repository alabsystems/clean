// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural self-calls in generalized field notation whose receiver is not
//! the first explicit argument (`e₁.evalAt k w` for `def Ex.evalAt (k : Int)
//! (w : Nat) : Ex → Int`), through the production entry
//! (`elaborate_decl_and_register`: elaborate, then the full kernel check).
//!
//! Lean 4.8.0 places the receiver with `addLValArg` (`Lean/Elab/App.lean`):
//! at the first explicit parameter whose type is headed by the receiver's
//! type, here the third. trust-ir's `Proofs/AYBridge.lean`
//! `TrustIrExpr.evalAt` is this shape, and the rest of that file depended on
//! it. Every definition below is accepted by the pinned Lean 4.8.0 binary and
//! every refusal is one it makes too (checked 2026-09-30).

use super::*;

fn register(env: &mut Environment, src: &str) -> Result<(), ElabError> {
    let decl = parse_decl_for_elab(src)?;
    crate::elaborate_decl_and_register(env, &decl).map(|_| ())
}

fn register_ok(env: &mut Environment, src: &str) {
    if let Err(err) = register(env, src) {
        panic!("should elaborate and kernel-check:\n{src}\n{err:?}");
    }
}

fn rfl_ok(env: &mut Environment, name: &str, lhs: &str, rhs: &str) {
    register_ok(env, &format!("theorem {name} : {lhs} = {rhs} := rfl"));
}

fn rfl_refused(env: &mut Environment, name: &str, lhs: &str, rhs: &str) {
    let src = format!("theorem {name} : {lhs} = {rhs} := rfl");
    assert!(
        register(env, &src).is_err(),
        "a false equation must be refused: {src}"
    );
    assert!(env.get_const(&Name::from_string(name)).is_none());
}

fn ex_env() -> Environment {
    let mut env = Environment::with_prelude();
    register_ok(
        &mut env,
        "inductive Ex where\n  | lit : Int → Ex\n  | add : Ex → Ex → Ex\n  | neg : Ex → Ex",
    );
    env
}

/// The receiver is the THIRD explicit argument, and one call changes a
/// prefix argument (`k + 1`), which Lean generalizes.
#[test]
fn test_recursive_dot_call_receiver_third_elaborates_and_computes() {
    let mut env = ex_env();
    register_ok(
        &mut env,
        "def Ex.evalAt (k : Int) (w : Nat) : Ex → Int
  | .lit v => v + k
  | .add e1 e2 => e1.evalAt k w + e2.evalAt (k + 1) w
  | .neg e => -(e.evalAt k w) + w",
    );
    rfl_ok(
        &mut env,
        "evalAt_add",
        "(Ex.add (.lit 1) (.lit 2)).evalAt 10 3",
        "24",
    );
    rfl_ok(
        &mut env,
        "evalAt_neg",
        "(Ex.neg (.lit 2)).evalAt 10 3",
        "-9",
    );
    rfl_refused(
        &mut env,
        "evalAt_false",
        "(Ex.add (.lit 1) (.lit 2)).evalAt 10 3",
        "13",
    );
}

/// The receiver is the second explicit argument, beside a dot call on a
/// receiver of ANOTHER type (`l.length` is `List.length`, not a self-call).
#[test]
fn test_recursive_dot_call_receiver_second_beside_foreign_dot_elaborates_and_computes() {
    let mut env = ex_env();
    register_ok(
        &mut env,
        "def Ex.count (k : Nat) : Ex → Nat
  | .lit _ => k
  | .add e1 e2 => e1.count k + e2.count k
  | .neg e => let l := [e, e]; l.length + e.count k",
    );
    rfl_ok(&mut env, "count_neg", "Ex.count 5 (.neg (.lit 1))", "7");
    rfl_ok(
        &mut env,
        "count_add",
        "Ex.count 5 (.add (.lit 1) (.neg (.lit 2)))",
        "12",
    );
    rfl_refused(&mut env, "count_false", "Ex.count 5 (.neg (.lit 1))", "5");
}

/// Refused because the recursion is not structural (Lean 4.8.0: "fail to
/// show termination"), and not registered. A refusal for any other reason —
/// an elaboration failure that never reached the recursion check — fails.
fn refused_non_structural(env: &mut Environment, name: &str, src: &str) {
    let err = match register(env, src) {
        Ok(()) => panic!("`{name}` recurses on a non-structural argument:\n{src}"),
        Err(err) => format!("{err}"),
    };
    assert!(
        ["recurs", "termination", "decreasing"]
            .iter()
            .any(|reason| err.contains(reason))
            && err.contains(name.rsplit('.').next().unwrap_or(name)),
        "`{name}` must be refused for its recursion, got: {err}"
    );
    assert!(env.get_const(&Name::from_string(name)).is_none());
}

/// Negative control: the receiver is the rebuilt scrutinee, not a
/// structural child. Lean 4.8.0: "fail to show termination". Placing the
/// receiver must not turn it into an induction-hypothesis call.
#[test]
fn test_recursive_dot_call_non_structural_receiver_is_refused() {
    let mut env = ex_env();
    refused_non_structural(
        &mut env,
        "Ex.loop",
        "def Ex.loop (k : Int) (w : Nat) : Ex → Int
  | .lit v => v + k
  | .add e1 e2 => e1.loop k w + e2.loop k w
  | .neg e => (Ex.neg e).loop k w",
    );
}

/// The same control with a VARIABLE receiver, so the call reaches the
/// receiver placement (`try_elab_recursive_dot_call` and the detector's
/// `placed_receiver` both need an identifier base; `(Ex.neg e).loop` never
/// gets there). `e'` is a local of type `Ex`, placed third as Lean places it,
/// and it is not a structural child: pinned Lean 4.8.0 refuses with "fail to
/// show termination … loop2 k w e'" (checked 2026-10-07).
#[test]
fn test_recursive_dot_call_variable_non_structural_receiver_is_refused() {
    let mut env = ex_env();
    refused_non_structural(
        &mut env,
        "Ex.loop2",
        "def Ex.loop2 (k : Int) (w : Nat) : Ex → Int
  | .lit v => v + k
  | .add e1 e2 => e1.loop2 k w + e2.loop2 k w
  | .neg e => let e' := Ex.neg e; e'.loop2 k w",
    );
}

// ------------------------------------------------- aliases and placements
//
// Every verdict below is the pinned Lean 4.8.0 binary's (2026-10-08,
// `scratchpad/r2fix-match/oracle/D.lean`, the same definitions). Lean's
// `typeMatchesBaseName` matches a parameter type by its head as written, else
// by the head of its `whnfR` (reducible transparency), and the receiver goes
// to the first explicit parameter that matches.

fn tr_env() -> Environment {
    let mut env = Environment::with_prelude();
    for src in [
        "inductive Tr where\n  | leaf : Nat → Tr\n  | node : Tr → Tr → Tr",
        "def SAlias := Tr",
        "@[reducible] def RAlias := Tr",
        "abbrev AAlias := Tr",
    ] {
        register_ok(&mut env, src);
    }
    env
}

/// A parameter typed by a SEMIREDUCIBLE alias of `Tr` is not a receiver slot
/// (`whnfR` does not unfold it), so `l.f a n` is `Tr.f a n l`. Before
/// 8049eae93 the placement used default-transparency `whnf`, which unfolds
/// the alias and put the receiver first.
#[test]
fn test_recursive_dot_call_semireducible_alias_parameter_is_skipped() {
    let mut env = tr_env();
    register_ok(
        &mut env,
        "def Tr.f (a : SAlias) (n : Nat) : Tr → Nat
  | .leaf v => v + n
  | .node l r => l.f a n + r.f a (n + 1) + 10",
    );
    let call = "Tr.f (Tr.leaf 0) 3 (.node (.leaf 1) (.leaf 2))";
    rfl_ok(&mut env, "f_val", call, "20");
    rfl_refused(&mut env, "f_false", call, "21");
}

/// Refused as the REORDERED call: a `RecursionOutsideFragment` whose detail
/// names what that call passes in the decreasing slot. The method-dot path
/// would have computed the call with the receiver in that slot instead.
fn refused_reordered(env: &mut Environment, name: &str, passes: &str, src: &str) {
    let err = match register(env, src) {
        Ok(()) => panic!("`{name}`: Lean places the receiver elsewhere and refuses:\n{src}"),
        Err(err) => err,
    };
    let text = format!("{err}");
    assert!(
        matches!(err, ElabError::RecursionOutsideFragment { .. })
            && text.contains(&format!("passes {passes} for")),
        "`{name}` must be refused as the reordered call passing {passes}, got: {text}"
    );
    assert!(env.get_const(&Name::from_string(name)).is_none());
}

/// A REDUCIBLE alias (`@[reducible] def`, `abbrev`) at explicit position 0
/// is the receiver slot, so `l.g a n` is `Tr.g l a n`: `a` lands in the
/// `Nat` slot and Lean reports "application type mismatch" (for `g2`, `r`
/// does). These were ACCEPTED as `Tr.g a n l` until 2026-10-08: a receiver
/// placed at position 0 kept the method-dot path, which substitutes the
/// induction hypothesis and so fills the decreasing (third) slot.
#[test]
fn test_recursive_dot_call_reducible_alias_at_position_zero_is_refused() {
    let mut env = tr_env();
    refused_reordered(
        &mut env,
        "Tr.g",
        "`n`",
        "def Tr.g (a : RAlias) (n : Nat) : Tr → Nat
  | .leaf v => v + n
  | .node l r => l.g a n + r.g a n",
    );
    refused_reordered(
        &mut env,
        "Tr.h",
        "`n`",
        "def Tr.h (a : AAlias) (n : Nat) : Tr → Nat
  | .leaf v => v + n
  | .node l r => l.h a n + r.h a n",
    );
    refused_reordered(
        &mut env,
        "Tr.g2",
        "a compound expression",
        "def Tr.g2 (a : RAlias) (n : Nat) : Tr → Nat
  | .leaf v => v + n
  | .node l r => l.g2 r (n + 1) + 1",
    );
}

/// The receiver lands at position 1 (the first `Tr` binder) and the
/// decreasing argument is the third: `l.m2 (n + 1) a` is `Tr.m2 (n + 1) l
/// a`, which Lean refuses ("fail to show termination"). Until 2026-10-08 the
/// reordered call declined and the method-dot path then accepted it as
/// `Tr.m2 (n + 1) a l`. `m3`, the same placement with the structural child
/// in the third slot, is Lean's call and computes Lean's value.
#[test]
fn test_recursive_dot_call_receiver_before_the_decreasing_argument() {
    let mut env = tr_env();
    refused_non_structural(
        &mut env,
        "Tr.m2",
        "def Tr.m2 (n : Nat) (a : Tr) : Tr → Nat
  | .leaf v => v + n
  | .node l r => l.m2 (n + 1) a + 1",
    );
    register_ok(
        &mut env,
        "def Tr.m3 (n : Nat) (a : Tr) : Tr → Nat
  | .leaf v => v + n
  | .node l r => l.m3 (n + 1) r + 1",
    );
    let call = "Tr.m3 1 (.leaf 7) (.node (.leaf 1) (.leaf 2))";
    rfl_ok(&mut env, "m3_val", call, "5");
    rfl_refused(&mut env, "m3_false", call, "4");
}

/// The receiver goes to position 0, a parameter typed by a REDUCIBLE alias
/// of `Tr`, and the call is structural on the third argument: `l.g3 a r` is
/// `Tr.g3 l a r`, which pinned Lean 4.8.0 accepts with value 3 below. Until
/// 2026-10-08 the method-dot path accepted it as `Tr.g3 a r l`, value 2: a
/// definition Lean accepts, computed with a different meaning. The FALSE twin
/// is exactly that old value.
#[test]
fn test_recursive_dot_call_reducible_alias_receiver_before_the_decreasing_argument_computes() {
    let mut env = tr_env();
    register_ok(
        &mut env,
        "def Tr.g3 (a : RAlias) (b : Tr) : Tr → Nat
  | .leaf v => v
  | .node l r => l.g3 a r + 1",
    );
    let call = "Tr.g3 (.leaf 5) (.leaf 6) (.node (.leaf 1) (.leaf 2))";
    rfl_ok(&mut env, "g3_val", call, "3");
    rfl_refused(&mut env, "g3_method_dot_value", call, "2");
}

/// OPEN, refused where Lean ACCEPTS (a completeness gap, safe direction):
/// `a : Tr` at position 0 takes the receiver, and the call is structural on
/// the third argument: `l.k2 a r` is `Tr.k2 l a r`, `= 3` on the input
/// below. Recursion detection never places a receiver at position 0
/// (`method_dot_receiver_pos`, the legacy reading records `l` and `a r` as
/// two calls), so no decreasing argument is found. Fails the day it is
/// accepted: check Lean's value then.
#[test]
fn test_recursive_dot_call_receiver_at_position_zero_before_the_decreasing_argument_is_refused_open_gap(
) {
    let mut env = tr_env();
    let src = "def Tr.k2 (a : Tr) (b : Tr) : Tr → Nat
  | .leaf v => v
  | .node l r => l.k2 a r + 1";
    let err = register(&mut env, src)
        .expect_err("open gap: Lean accepts `Tr.k2` (value 3) but Clean refuses it");
    assert!(
        matches!(err, ElabError::RecursionOutsideFragment { .. }),
        "`Tr.k2` must be refused for its recursion, got: {err}"
    );
    assert!(env.get_const(&Name::from_string("Tr.k2")).is_none());
}
