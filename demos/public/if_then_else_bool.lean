-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Public demo: if-then-else with BOOL conditions (e.g. `x == y`, `n <= 0`).
--
-- Before the fix, a structured `if` was macro-expanded into an `ite`
-- application before reaching `elab_if`, and `ite : (c : Prop) → [Decidable c] →
-- α → α → α` rejected a `Bool` condition ("expected Sort(Zero), got Bool").
-- Now `if` is routed to `elab_if` (bypassing the macro roundtrip, like
-- Match/IfLet), which lowers a Bool condition to `Bool.rec` — no `Decidable`
-- instance needed, and it reduces definitionally (so the `rfl` proofs hold).
-- trust-ir's operational semantics use Bool conditions pervasively, so this is
-- on the path to Clean verifying trust-ir directly.

-- literal Bool condition
def lit : Nat := if true then 7 else 9
theorem lit_eq : lit = 7 := rfl

-- Bool condition via `==`
def classify (n : Nat) : Nat := if n == 0 then 100 else 200
theorem classify_0 : classify 0 = 100 := rfl
theorem classify_5 : classify 5 = 200 := rfl

-- bare Bool argument
def pick (b : Bool) : Nat := if b then 1 else 0
theorem pick_t : pick true = 1 := rfl
theorem pick_f : pick false = 0 := rfl

-- if-then-else INSIDE a match arm (the trust-ir conditional-logic shape)
def step (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | _ => if n == 1 then 10 else 20
theorem step_1 : step 1 = 10 := rfl
theorem step_2 : step 2 = 20 := rfl
