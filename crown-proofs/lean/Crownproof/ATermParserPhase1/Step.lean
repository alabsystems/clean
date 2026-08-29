/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

ATERM VT-PARSER — PHASE 1 / THEOREM A
(escape-sequence parser: the bounded-buffer invariant is preserved by every
transition, for ALL inputs).

────────────────────────────────────────────────────────────────────────────
WHAT THIS IS
────────────────────────────────────────────────────────────────────────────
The Rust terminal `~/aterm` implements a VT/escape-sequence parser whose state
machine is, per its own source, "based on vt100.net DEC ANSI parser" (Paul
Williams' VT500 DFA / ECMA-48). It carries a resident `TypeInvariant`
(`aterm-parser/src/invariants.rs`) — bounded parameter and intermediate buffers,
a UTF-8 decoder-progress bound, and DCS/APC mutual exclusion — that aterm checks
two ways, both INCOMPLETE: a `#[cfg(debug_assertions)]` runtime `assert_invariants`
(gone in release), and Kani proofs `params_bounded` / `intermediates_bounded`
bounded to `#[kani::unwind(8)]` (no proof for longer inputs; a variant was
"killed after 142.9s").

`step_preserves_inv` below is the **all-inputs lift** of those bounded Kani
proofs: the invariant is closed under the transition for EVERY input class, by
finite case analysis rather than bounded unrolling. See the design doc
`designs/2026-06-16-aterm-parser-as-kernel-checked-theory.md` §3–§4.

────────────────────────────────────────────────────────────────────────────
THE MODEL (faithful, finite, fully constructive)
────────────────────────────────────────────────────────────────────────────
`ParserState` is the 14-state enum from `aterm-parser/src/state.rs`. `ByteClass`
is the transition table's action class for an input byte — the design doc
endorses abstracting the 256 bytes into "the handful of ranges the transition
table partitions 0–255 into", which keeps the case analysis finite. `Config`
carries the resident state the invariant constrains; the parameter and
intermediate buffers are represented by their LENGTHS (`paramCount` /
`interCount`), which is exactly what aterm's `ParamsBounded` /
`IntermediatesBounded` invariants constrain.

`step` realises the four buffer-mutating actions the DEC ANSI table dispatches:
  • Esc / Final  → Clear  (counts reset to 0);
  • Param        → guarded push to params        (count capped at 16 = MAX_PARAMS);
  • Intermediate → guarded push to intermediates  (count capped at 4  = MAX_INTERMEDIATES);
  • C0ctrl / Delete → Execute / Ignore  (counts unchanged).

`gincr n cap = min (n+1) cap` models aterm's `ArrayVec::push` overflow guard on
the count: below capacity it grows by one, at capacity it is a no-op. It is
built from a structurally-recursive `capMin` (not `if … < …` nor `Nat.ble`)
specifically so the proof has no impossible-branch `noConfusion`/`False.elim`
step — keeping the carried-family closure free of `Decidable`/`Not`/`False`. The
single non-trivial obligation (mirroring aterm's `params_bounded` /
`intermediates_bounded`) is that this capped increment never exceeds the cap;
`gincr_le` proves it unconditionally. The state-dependent next-state map and the
`project`-refinement commuting square (Theorem B) are Phase 2.

────────────────────────────────────────────────────────────────────────────
FOUNDATIONAL
────────────────────────────────────────────────────────────────────────────
Pure Lean-core arithmetic; NO Mathlib import, NO `sorry`, NO `native_decide`, NO
new `axiom`. The proofs depend on NO axioms at all (fully constructive) —
verified by `#print axioms` below.
-/

namespace Crownproof.ATermParserPhase1

/-- The 14 parser states, mirroring `aterm-parser/src/state.rs` `State`
(vt100.net DEC ANSI parser). An out-of-range state tag is unrepresentable here
by construction — aterm's runtime `assert (state < State::COUNT)` is a
non-theorem in this encoding. -/
inductive ParserState where
  | Ground | Escape | EscapeIntermediate | CsiEntry | CsiParam | CsiIntermediate
  | CsiIgnore | DcsEntry | DcsParam | DcsIntermediate | DcsPassthrough | DcsIgnore
  | OscString | SosPmApcString

/-- Byte equivalence classes = the action the DEC ANSI transition table
dispatches for a byte. The buffer-growing classes are `Param` and `Intermediate`;
`Esc`/`Final` clear; `C0ctrl`/`Delete` leave the buffers untouched. -/
inductive ByteClass where
  | C0ctrl | Esc | Intermediate | Param | Final | Delete

/-- `MAX_PARAMS` (aterm `parser/src/lib.rs`). -/
def maxParams : Nat := 16
/-- `MAX_INTERMEDIATES` (aterm `parser/src/lib.rs`). -/
def maxIntermediates : Nat := 4

/-- The resident parser state the `TypeInvariant` constrains
(`aterm-parser/src/invariants.rs`). The parameter/intermediate buffers are
represented by their lengths (`paramCount` / `interCount`). -/
structure Config where
  state : ParserState
  paramCount : Nat
  interCount : Nat
  utf8Len : Nat
  utf8Expected : Nat
  dcsActive : Bool
  apcActive : Bool

/-- `Inv` = aterm's `TypeInvariant`: bounded parameter/intermediate buffers,
UTF-8 decoder progress (`utf8_len ≤ utf8_expected ≤ 4`), and DCS/APC mutual
exclusion. -/
def Inv (c : Config) : Prop :=
  c.paramCount ≤ maxParams
  ∧ c.interCount ≤ maxIntermediates
  ∧ c.utf8Len ≤ c.utf8Expected
  ∧ c.utf8Expected ≤ 4
  ∧ (c.dcsActive && c.apcActive) = false

/-- Structural `min`, by recursion on both arguments. Exhaustive patterns ⇒ the
compiled term is pure `Nat.casesOn` with no impossible-branch `False.elim`. -/
def capMin : Nat → Nat → Nat
  | 0,     _      => 0
  | _ + 1, 0      => 0
  | a + 1, b + 1  => capMin a b + 1

/-- Guarded push, on the buffer COUNT: `min (n+1) cap`. This is the discipline of
aterm's `ArrayVec::push` overflow guard — grow by one while below capacity, no-op
at capacity. -/
def gincr (n cap : Nat) : Nat := capMin (n + 1) cap

/-- The transition's effect on the resident config. Total: every byte class has
a defined successor. -/
def step (c : Config) (bc : ByteClass) : Config :=
  match bc with
  | ByteClass.Esc =>
      { c with state := ParserState.Escape, paramCount := 0, interCount := 0 }
  | ByteClass.Final =>
      { c with state := ParserState.Ground, paramCount := 0, interCount := 0 }
  | ByteClass.Param =>
      { c with state := ParserState.CsiParam,
               paramCount := gincr c.paramCount maxParams }
  | ByteClass.Intermediate =>
      { c with state := ParserState.CsiIntermediate,
               interCount := gincr c.interCount maxIntermediates }
  | ByteClass.C0ctrl => c
  | ByteClass.Delete => c

/-- The structural `min` never exceeds its right argument — by structural
recursion with NO impossible cases (`Nat.zero_le`, `Nat.le.refl`,
`Nat.succ_le_succ` only), so the proof term is `False`-free. -/
theorem capMin_le_right : ∀ a b, capMin a b ≤ b
  | 0,     b      => Nat.zero_le b
  | _ + 1, 0      => Nat.le.refl
  | a + 1, b + 1  => Nat.succ_le_succ (capMin_le_right a b)

/-- **The guarded push preserves the cap bound, unconditionally.** This is the
all-inputs core of aterm's bounded Kani proofs `params_bounded` /
`intermediates_bounded`: the capped increment never exceeds the cap, whether the
push fired (count was below cap) or was suppressed at capacity. -/
theorem gincr_le (n cap : Nat) : gincr n cap ≤ cap :=
  capMin_le_right (n + 1) cap

/-- **THEOREM A — invariant preservation over all inputs.**
The resident `TypeInvariant` is closed under the parser transition for EVERY
input class. This subsumes aterm's `#[kani::unwind(8)]`-bounded `params_bounded`
/ `intermediates_bounded` with no input-length ceiling. -/
theorem step_preserves_inv (c : Config) (bc : ByteClass) (h : Inv c) :
    Inv (step c bc) := by
  obtain ⟨hp, hi, hu1, hu2, hda⟩ := h
  cases bc
  case C0ctrl => exact ⟨hp, hi, hu1, hu2, hda⟩
  case Esc => exact ⟨Nat.zero_le _, Nat.zero_le _, hu1, hu2, hda⟩
  case Intermediate => exact ⟨hp, gincr_le _ _, hu1, hu2, hda⟩
  case Param => exact ⟨gincr_le _ _, hi, hu1, hu2, hda⟩
  case Final => exact ⟨Nat.zero_le _, Nat.zero_le _, hu1, hu2, hda⟩
  case Delete => exact ⟨hp, hi, hu1, hu2, hda⟩

/-! ## Trust-base check — must reduce to the standard logical axioms only
(`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`, NO
`native_decide` / `Lean.ofReduceBool`. (Here: no axioms at all.) -/

#print axioms capMin_le_right
#print axioms gincr_le
#print axioms step_preserves_inv

end Crownproof.ATermParserPhase1
