/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

ATERM VT-PARSER — PHASE 2 / THEOREM B
(escape-sequence parser: the concrete transition REFINES the abstract model —
the refinement commuting square, for ALL inputs).

────────────────────────────────────────────────────────────────────────────
WHAT THIS IS
────────────────────────────────────────────────────────────────────────────
The Rust terminal `~/aterm` already carries a Tier-1 conformance binding for its
VT parser: `impl Refines<ParserModel> for Parser`
(`aterm-parser/src/tests/refinement.rs`) defines an abstraction map
`project : Parser → ParserModel` onto the TLA+ spec variables
`{ state, param_count = params.len(), intermediate_count = intermediates.len(),
current_param }` — explicitly FORGETTING the UTF-8 / OSC / APC sub-state
("Implementation details … are excluded"). But aterm only spot-checks the map on
THREE concrete traces (`test_initial_state_projects_to_ground`,
`test_csi_entry_projects_state_and_params`, `test_ground_after_complete_sequence`).
The forward-simulation THEOREM — that the abstraction COMMUTES with the
transition on *every* input — is never proved. aterm's own roadmap names that
missing rung "Tier-2: all-inputs refinement (pending toolchain)".

`parser_refines_model` below is that rung, kernel-checked: the refinement
commuting square

    project (step c bc)  =  stepA (project c) bc      (∀ c, ∀ bc)

i.e. abstracting-then-stepping equals stepping-then-abstracting. This is the
clean-saas §5.1 forward simulation specialised to a finite DFA: the simulation
relation is `Match σ τ := (project σ = τ)`, and the four §5.1 `CheckKind`s
collapse to component agreement (`state` = ControlFlow, the two counts =
DataFlow) with termination trivial (every `step`/`stepA` is total).

────────────────────────────────────────────────────────────────────────────
WHY THE SQUARE IS NOT VACUOUS
────────────────────────────────────────────────────────────────────────────
`stepA` is the transition on the ABSTRACT state alone — it never sees
`utf8Len`/`utf8Expected`/`dcsActive`/`apcActive`. The square therefore asserts a
real, falsifiable property: the concrete `step`'s effect on the RETAINED fields
(`state`, the two counts) depends ONLY on the retained fields — `step` factors
through `project`. Had `step`'s next-state or a count update read a forgotten
field, no `stepA` over the abstract state could match it and the `rfl` would
fail. That it holds is the soundness of the abstraction (here in fact a
bisimulation on the retained fields). The proof is finite (`cases bc`) and, like
Theorem A, depends on NO axioms.

NOTE (faithfulness): aterm's `ParserModel` also carries `current_param` (the
in-progress accumulator). The Phase-1 `Config` represents the buffers by their
COUNTS and does not track that accumulator, so this projection captures the three
model fields the count-model represents (`state`, `param_count`,
`intermediate_count`); adding `current_param` is a strict refinement for later.
The UTF-8 exclusion matches aterm `refinement.rs` exactly.
-/

import Crownproof.ATermParserPhase1.Step

namespace Crownproof.ATermParserPhase1

/-- aterm's abstract `ParserModel` (`refinement.rs`), over the fields the
count-model represents: the parser state plus the two bounded buffer counts. The
UTF-8 / DCS / APC sub-state is intentionally forgotten (matches aterm). -/
structure ParserModel where
  state : ParserState
  paramCount : Nat
  interCount : Nat

/-- The abstraction map (`= refinement.rs::project`, restricted to the retained
fields): drop the UTF-8 / DCS / APC sub-state, keep state + the two counts. -/
def project (c : Config) : ParserModel :=
  { state := c.state, paramCount := c.paramCount, interCount := c.interCount }

/-- The ABSTRACT transition: the spec's step on the abstract state ALONE. It has
no access to the forgotten sub-state, so it can only be written as a function of
`{ state, paramCount, interCount }`. It mirrors the DEC ANSI table's effect on
those fields (the same actions as `step`). -/
def stepA (m : ParserModel) (bc : ByteClass) : ParserModel :=
  match bc with
  | ByteClass.Esc =>
      { m with state := ParserState.Escape, paramCount := 0, interCount := 0 }
  | ByteClass.Final =>
      { m with state := ParserState.Ground, paramCount := 0, interCount := 0 }
  | ByteClass.Param =>
      { m with state := ParserState.CsiParam,
               paramCount := gincr m.paramCount maxParams }
  | ByteClass.Intermediate =>
      { m with state := ParserState.CsiIntermediate,
               interCount := gincr m.interCount maxIntermediates }
  | ByteClass.C0ctrl => m
  | ByteClass.Delete => m

/-- **THEOREM B — the refinement commuting square, over all inputs.**
Abstracting then stepping equals stepping then abstracting, for every config and
every byte class. This is the all-inputs lift of aterm's three Tier-1 trace
conformance tests into a kernel-checked Tier-2 forward simulation. -/
theorem parser_refines_model (c : Config) (bc : ByteClass) :
    project (step c bc) = stepA (project c) bc := by
  cases bc <;> rfl

/-- The abstract analogue of `Inv`: the abstract model's bounded-buffer
invariant (the two count bounds — all the abstract state carries). -/
def InvA (m : ParserModel) : Prop :=
  m.paramCount ≤ maxParams ∧ m.interCount ≤ maxIntermediates

/-- The abstraction map TRANSPORTS the concrete invariant: a config satisfying
the resident `TypeInvariant` projects to an abstract model satisfying `InvA`.
This bridges Theorem A (Phase 1) to the abstract model. -/
theorem project_preserves_inv (c : Config) (h : Inv c) : InvA (project c) := by
  obtain ⟨hp, hi, _, _, _⟩ := h
  exact ⟨hp, hi⟩

/-- **The abstract spec is itself invariant-preserving, over all inputs** — the
abstract analogue of Theorem A, proved directly on the abstract model (reusing
`gincr_le`). With `parser_refines_model` + `project_preserves_inv` this gives an
independent route to the projected concrete bound. -/
theorem stepA_preserves_invA (m : ParserModel) (bc : ByteClass) (h : InvA m) :
    InvA (stepA m bc) := by
  obtain ⟨hp, hi⟩ := h
  cases bc
  case C0ctrl => exact ⟨hp, hi⟩
  case Esc => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  case Intermediate => exact ⟨hp, gincr_le _ _⟩
  case Param => exact ⟨gincr_le _ _, hi⟩
  case Final => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  case Delete => exact ⟨hp, hi⟩

/-! ## Trust-base check — axiom closure must be foundational-only (here: none). -/

#print axioms parser_refines_model
#print axioms project_preserves_inv
#print axioms stepA_preserves_invA

end Crownproof.ATermParserPhase1
