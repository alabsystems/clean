// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `cases h` on an equation runs Lean's `unifyEqs?` (G82, ledger (152);
//! closes (81)), and `injection` reads its field equations off
//! `noConfusionType`. Driven through the production file loop over the
//! built-in prelude.
//!
//! Every verdict here was measured against the pinned Lean 4.8.0 binary on
//! 2026-10-16 (`reports/trust-ir-semantics-probe/repros/G82-*.lean` and the
//! lane's scratch fixtures): it accepts every `accepted` declaration, rejects
//! every twin with the error quoted beside it, and ACCEPTS the two pinned
//! gaps, which Clean refuses by name.

use crate::test_support::file_verdicts::{run_file, verdict_of};

type Verdicts = Vec<(String, Result<(), String>)>;

fn accepted(verdicts: &Verdicts, names: &[&str]) {
    for name in names {
        if let Err(err) = verdict_of(verdicts, name) {
            panic!("`{name}` must elaborate (pinned Lean 4.8.0 accepts it): {err}");
        }
    }
}

#[test]
fn dependent_goal_closes_only_for_distinct_constructors() {
    let source = "
def probeBit (_ : Nat) : Bool := false
theorem dependentGoal (n : Nat) (h : probeBit n = true)
    (P : (probeBit n = true) → Prop) : P h := by
  cases h
";
    accepted(&run_file(source), &["dependentGoal"]);
    let same_constructor = source.replace(":= false", ":= true");
    refused(&run_file(&same_constructor), "dependentGoal");
    let opaque_bit = source.replace("def probeBit", "@[irreducible] def probeBit");
    refused(&run_file(&opaque_bit), "dependentGoal");
}

fn refused<'a>(verdicts: &'a Verdicts, name: &str) -> &'a str {
    match verdict_of(verdicts, name) {
        Ok(()) => panic!("`{name}` must be refused (pinned Lean 4.8.0 rejects it)"),
        Err(err) => err,
    }
}

const POSITIVE: &str = "\
theorem t1 {a b : Nat} {x y : Nat} (h : (Except.ok (a, b) : Except String (Nat × Nat)) = .ok (x, y)) : x = a := by
  cases h
  rfl

theorem t2 {a b x y : Nat} (h : (a, b) = (x, y)) : y = b := by
  cases h
  rfl

theorem t3 {a x : Nat} (h : some a = some x) : x = a := by
  cases h
  rfl

theorem t4 {a b : Nat} {p : Nat × Nat} (h : (Except.ok (a, b) : Except String (Nat × Nat)) = .ok p) : p.1 = a := by
  cases h
  rfl

theorem t5 {a b c x y z : Nat} (h : (a, b, c) = (x, y, z)) : x + y + z = a + b + c := by
  cases h
  rfl

structure St where
  n : Nat
  m : Nat

theorem t6 {s s' : St} {k : Nat} (h : (Except.ok (k, { s with n := s.n + 1 }) : Except String (Nat × St)) = .ok (5, s')) : s'.n = s.n + 1 ∧ k = 5 := by
  cases h
  exact ⟨rfl, rfl⟩

theorem t7 {a b x y : Nat} (h : some (a, b) = some (x, y)) : (x, y) = (a, b) := by
  cases h
  rfl

theorem t8 {a : Nat} (h : some a = none) : False := by
  cases h

theorem t9 {a b x y : Nat} (h : (a, b) = (x, y)) : ∀ z : Nat, z + y = z + b := by
  cases h
  intro z
  rfl

structure DF where
  n : Nat
  v : Fin n

theorem t10 {n m : Nat} {v : Fin n} {w : Fin m} (h : DF.mk n v = DF.mk m w) : HEq v w := by
  cases h
  exact HEq.rfl

theorem t11 (y x : Nat) (p : x = 3) (h : x = y) : y = 3 := by
  cases h
  show y = 3
  exact p

theorem t12 (x : Nat) (h : x = x) : x = x := by
  cases h
  rfl

theorem t13 {a b x y : Nat} (h : HEq (a, b) (x, y)) : x = a := by
  cases h
  rfl

theorem t15 (x : Nat) (h : 5 = x + 1) : x = 4 := by
  cases h
  rfl

theorem t16 (a b : Nat) (h : [a, b] = [1, 2]) : a = 1 := by
  cases h
  rfl

theorem cases_ctor_eq (ys : List Nat)
    (h : (Except.ok [] : Except String (List Nat)) = Except.ok ys) : ys = [] := by
  cases h
  rfl

theorem i1 {a b x y : Nat} (h : (a, b) = (x, y)) : a = x := by
  injection h

theorem i2 {a b : Nat} {ha : a > 0} {hb : b > 0} (h : (⟨a, ha⟩ : {n : Nat // n > 0}) = ⟨b, hb⟩) : a = b := by
  injection h

theorem o1 {a b x y : Nat} (h : (a, b) = (x, y)) : x = a := by
  rcases h with ⟨⟩
  rfl

theorem o2 {a b x y : Nat} (h : (a, b) = (x, y)) : x = a := by
  obtain ⟨⟩ := h
  rfl

def MyEq (a b : Nat × Nat) : Prop := a = b
theorem o4 {a b x y : Nat} (h : MyEq (a, b) (x, y)) : x = a := by
  cases h
  rfl

theorem o7 {a b x y : Nat} (h : (a, b) = (x, y)) : x = a := by
  cases h with
  | refl => rfl

theorem a1 {x : Nat} (h : x = 5) : x = 5 := by
  cases h with
  | refl => rfl

def g (n : Nat) : Option Nat := some n
theorem w1 {a b : Nat} (h : g a = g b) : a = b := by
  cases h
  rfl
";

/// The repro shapes (trust-ir `Sem.bindFreshPair_ok`'s `Except.ok (pair,
/// {s with …}) = Except.ok (ids, s')` among them), nested constructors,
/// distinct constructors, a dependent field (`HEq` in `noConfusionType`),
/// literals, the direction of a local-local equation, and `injection` over a
/// parameterized type and over a `Prop` field.
#[test]
fn test_cases_on_constructor_equations_unifies_like_lean() {
    let verdicts = run_file(POSITIVE);
    accepted(
        &verdicts,
        &[
            "t1",
            "t2",
            "t3",
            "t4",
            "t5",
            "t6",
            "t7",
            "t8",
            "t9",
            "t10",
            "t11",
            "t12",
            "t13",
            "t15",
            "t16",
            "cases_ctor_eq",
            "i1",
            "i2",
            "o1",
            "o2",
            "o4",
            "o7",
            "a1",
            "w1",
        ],
    );
}

const NEGATIVE: &str = "\
theorem n1 {a b x y : Nat} (h : (a, b) = (x, y)) : x = b := by
  cases h
  rfl

axiom f : Nat → Nat
theorem n2 {a b : Nat} (h : f a = f b) : a = b := by
  cases h
  rfl

structure DF where
  n : Nat
  v : Fin n

theorem n3 {n m : Nat} {v : Fin n} {w : Fin m} (h : DF.mk n v = DF.mk m w) : v.val = w.val + 1 := by
  cases h
  rfl

theorem n4 {a b x y : Nat} (h : (a, b) = (x, y)) : False := by
  cases h

theorem n5 (y x : Nat) (p : x = 3) (h : x = y) : y = 3 := by
  cases h
  show x = 3
  exact p

theorem n6 {a : Nat} (h : some a = some 3) : a = 4 := by
  cases h
  rfl

theorem o1n {a b x y : Nat} (h : (a, b) = (x, y)) : x = b := by
  rcases h with ⟨⟩
  rfl

theorem o2n {a b x y : Nat} (h : (a, b) = (x, y)) : x = b := by
  obtain ⟨⟩ := h
  rfl

def MyEq (a b : Nat × Nat) : Prop := a = b
theorem o4n {a b x y : Nat} (h : MyEq (a, b) (x, y)) : x = b := by
  cases h
  rfl

theorem o7n {a b x y : Nat} (h : (a, b) = (x, y)) : x = a := by
  cases h with
  | foo => rfl

@[irreducible] def gi (n : Nat) : Option Nat := some n
theorem w2 {a b : Nat} (h : gi a = gi b) : a = b := by
  cases h
  rfl
";

/// The twins. Pinned Lean 4.8.0: n1 `rfl` fails at `a = b`; n2 "dependent
/// elimination failed, failed to solve equation f b = f a"; n3 `rfl` fails
/// at `↑v = ↑v + 1`; n4 unsolved goals `False`; n5 "unknown identifier 'x'"
/// (the later-declared `x` was eliminated — Clean before this change kept
/// `x` and ACCEPTED n5); n6 `rfl` fails at `3 = 4`; o1n, o2n, o4n (the
/// `rcases … ⟨⟩`, `obtain ⟨⟩` and `def`-wrapped routes) `rfl` fails at
/// `a = b`; o7n "invalid alternative name 'foo'"; w2 "dependent elimination
/// failed, failed to solve equation gi b = gi a".
#[test]
fn test_cases_on_constructor_equations_twins_are_refused() {
    let verdicts = run_file(NEGATIVE);
    for name in ["n1", "n3", "n4", "n5", "n6", "o1n", "o2n", "o4n"] {
        let err = refused(&verdicts, name);
        assert!(
            !err.contains("dependent elimination") && !err.contains("neither side"),
            "`{name}` must fail AFTER `cases` unified the equation, as in Lean: {err}"
        );
    }
    refused(&verdicts, "o7n");
    let err = refused(&verdicts, "n2");
    assert!(
        err.contains("dependent elimination failed"),
        "`f a = f b` with an opaque `f` is Lean's dependent elimination failure: {err}"
    );
    // The `@[irreducible]` twin of the positive `w1`: Lean's `whnf` keeps
    // `gi` folded, so the equation is unsolvable; a transparency-blind
    // `whnf` would unfold it to `some a = some b` and accept.
    let err = refused(&verdicts, "w2");
    assert!(
        err.contains("dependent elimination failed"),
        "`gi a = gi b` with an irreducible `gi` is Lean's dependent elimination failure: {err}"
    );
}

const GAPS: &str = "\
theorem g1 (n : Nat) (h : n = n + 1) : False := by
  cases h

theorem g2 {a b x y : Nat} (h : (a, b) = (x, y)) (q : h = h) : True := by
  cases h
  trivial
";

/// OPEN, pinned as named refusals (pinned Lean 4.8.0 ACCEPTS both): Lean's
/// `acyclic` step (`n = n + 1` refuted through `sizeOf`) and the final
/// `h := Eq.refl` substitution when another hypothesis mentions `h` are not
/// implemented. Each assertion fails the day its step lands.
#[test]
fn test_cases_unify_eqs_open_steps_are_refused_by_name() {
    let verdicts = run_file(GAPS);
    let err = refused(&verdicts, "g1");
    assert!(
        err.contains("acyclic"),
        "g1 names the missing `acyclic` step: {err}"
    );
    let err = refused(&verdicts, "g2");
    assert!(
        err.contains("Eq.refl"),
        "g2 names the missing `h := Eq.refl` step: {err}"
    );
}

const CONSUMED: &str = "\
theorem q1 {x : Nat} (h : x = 5) : x = 5 ∧ True := by
  cases h
  refine ⟨?_, ?_⟩
  · rfl
  · trivial

theorem q2 {x : Nat} (h : x = 5) : x = 5 ∧ True := by
  subst h
  refine ⟨?_, ?_⟩
  · rfl
  · trivial

theorem q3 {a b x y : Nat} (h : (a, b) = (x, y)) : x = a ∧ True := by
  cases h
  refine ⟨?_, ?_⟩
  · rfl
  · trivial

theorem z2 (y : Nat) (q : y = y) (h : y = 5) : 5 = 5 := by
  subst h
  exact q

theorem z3 {a b x y : Nat} (h : (a, b) = (x, y)) (q : x = a) : x = a := by
  cases h
  exact q

theorem z6 (x : Nat) (h : x = x) : x = x := by
  cases h
  exact h

theorem z7 (x : Nat) (h : x = x) : x = x := by
  clear h
  exact h

theorem z8 {a b : Nat} (h : (a, b) = (a, b)) : (a, b) = (a, b) := by
  cases h
  exact h

theorem z9 (P : Prop) (h : P) : P := by
  revert h
  intro h2
  exact h

theorem z10 (a b : Prop) (h : a ∧ b) : a := by
  cases h
  exact h.1
";

/// A declaration binder a tactic consumed is out of scope for later tactic
/// terms (`crate::infer::elab_tactic_consumed`). q1–q3 (`refine ⟨?_, ?_⟩`
/// after `cases`/`subst` eliminated a binder; `Sem.bindFreshPair_ok`'s shape)
/// and z2/z3 (a dependent hypothesis re-introduced under its own name) are
/// accepted by pinned Lean 4.8.0. z6, z7 and z8 name the consumed `h`: Lean
/// reports "unknown identifier 'h'"; Clean resolved the stale binder — z7
/// (`clear h; exact h`) was ACCEPTED before this change, and z6/z8 would have
/// been once `cases h` clears a trivial equation. z9 (`revert h; intro h2;
/// exact h`) and z10 (`cases h` on `h : a ∧ b`, then `exact h.1`) are round-5
/// lane B's s8 and s9, found ACCEPTED on its branch and refused here since the
/// round-6 integration (pinned Lean 4.8.0: "unknown identifier 'h'", measured
/// 2026-10-17); z7 is its s6.
#[test]
fn test_consumed_declaration_binders_are_out_of_scope() {
    let verdicts = run_file(CONSUMED);
    accepted(&verdicts, &["q1", "q2", "q3", "z2", "z3"]);
    for name in ["z6", "z7", "z8", "z9", "z10"] {
        let err = refused(&verdicts, name);
        assert!(
            !err.contains("dependent elimination") && !err.contains("neither side"),
            "`{name}` must fail on the consumed name, after the elimination: {err}"
        );
    }
    // The verdict string is the error's `Debug` form
    // (`UnknownIdentWithSuggestions { name: "h", … }`).
    for name in ["z9", "z10"] {
        let err = refused(&verdicts, name);
        assert!(
            err.contains("UnknownIdent") && err.contains("name: \"h\""),
            "`{name}` must name the consumed `h`, as Lean's \"unknown identifier 'h'\": {err}"
        );
    }
}
