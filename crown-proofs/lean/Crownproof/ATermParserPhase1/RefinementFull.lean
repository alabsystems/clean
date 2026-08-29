/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

ATERM VT-PARSER — PHASE 2.5 / THEOREM B⁺
(the COMPLETE refinement square: all four clean-saas §5.1 CheckKinds, over a model
that matches aterm's `ParserModel` field-for-field).

────────────────────────────────────────────────────────────────────────────
WHAT THIS CLOSES
────────────────────────────────────────────────────────────────────────────
Phase 2 (`RefinementB`) proved the refinement square over `{state, paramCount,
interCount}` and discharged three §5.1 CheckKinds (ControlFlow + DataFlow;
Termination trivial). Its review flagged two honestly-disclosed gaps:

  1. aterm's `ParserModel` (`aterm-parser/src/tests/refinement.rs`) carries a
     FOURTH field, `current_param` (the in-progress accumulator) — Phase 2 dropped
     it. CLOSED here: `ConfigF`/`ParserModelF` carry `curParam`, so `projectF`
     matches aterm's `ParserModel` field-for-field {state, param_count,
     intermediate_count, current_param}.
  2. `step`/`stepA` emitted no action, so §5.1's `CheckKind::ReturnValue` (the
     emitted-`ActionType` edge) was out of scope. CLOSED here: `stepF` emits an
     `ActionType` via `actionOf`, and the square compares it — discharging the
     FOURTH CheckKind. The action edge is NON-TRIVIAL: `actionOf` is
     STATE-DEPENDENT (a `Final` byte dispatches CSI only inside a CSI sequence —
     `aterm-parser/src/table`), and `state` is a RETAINED field; had the action
     read a forgotten field the square's `rfl` would fail.

A `Separator` byte class is added (the DEC ANSI `;`/`:` that finalizes the current
parameter) so both the count (`paramCount`, grown on a separator commit) and the
accumulator (`curParam`, grown on a digit) are exercised — matching aterm's
`Param` (accumulate) vs separator-commit semantics.

Fully constructive (NO axioms); reuses Phase-1 `capMin`/`gincr`/`gincr_le`.
-/

import Crownproof.ATermParserPhase1.Step

namespace Crownproof.ATermParserPhase1.Full

open Crownproof.ATermParserPhase1 (ParserState maxParams maxIntermediates gincr gincr_le)

/-- Saturating cap for the in-progress accumulator. aterm finalizes a parameter to
`u16`, so the accumulator's standing bound is `u16::MAX`. -/
def maxParamVal : Nat := 65535

/-- Byte equivalence classes for the full model: the Phase-1 set plus `Separator`
(the DEC ANSI `;`/`:` that commits the current parameter into the count). -/
inductive ByteClassF where
  | C0ctrl | Esc | Intermediate | Param | Separator | Final | Delete

/-- DEC ANSI action classes (the subset these byte classes dispatch), mirroring
`aterm-parser/src/table/types.rs` `ActionType`. -/
inductive ActionType where
  | Execute | Clear | Collect | Param | CsiDispatch | Ignore

/-- Full resident state: the Phase-1 bounded-count state PLUS the in-progress
parameter accumulator `curParam` (aterm's `current_param`). -/
structure ConfigF where
  state : ParserState
  paramCount : Nat
  interCount : Nat
  curParam : Nat
  utf8Len : Nat
  utf8Expected : Nat
  dcsActive : Bool
  apcActive : Bool

/-- aterm's `ParserModel`, ALL FOUR fields {state, param_count, intermediate_count,
current_param}. The UTF-8 / DCS / APC sub-state is forgotten (matches aterm). -/
structure ParserModelF where
  state : ParserState
  paramCount : Nat
  interCount : Nat
  curParam : Nat

/-- The abstraction map = aterm `refinement.rs::project`, now field-for-field. -/
def projectF (c : ConfigF) : ParserModelF :=
  { state := c.state, paramCount := c.paramCount,
    interCount := c.interCount, curParam := c.curParam }

/-- `Inv` = aterm's `TypeInvariant`, extended with `CurrentParamBounded`
(`curParam ≤ maxParamVal` — aterm's saturating accumulator bound). -/
def InvF (c : ConfigF) : Prop :=
  c.paramCount ≤ maxParams
  ∧ c.interCount ≤ maxIntermediates
  ∧ c.curParam ≤ maxParamVal
  ∧ c.utf8Len ≤ c.utf8Expected
  ∧ c.utf8Expected ≤ 4
  ∧ (c.dcsActive && c.apcActive) = false

/-- The action the transition table dispatches for `(state, byte class)`.
STATE-DEPENDENT: a `Final` byte dispatches a CSI sequence only inside one,
otherwise it is just executed — exactly the DEC ANSI table's state×byte action. -/
def actionOf (s : ParserState) (bc : ByteClassF) : ActionType :=
  match bc with
  | ByteClassF.C0ctrl => ActionType.Execute
  | ByteClassF.Esc => ActionType.Clear
  | ByteClassF.Intermediate => ActionType.Collect
  | ByteClassF.Param => ActionType.Param
  | ByteClassF.Separator => ActionType.Param
  | ByteClassF.Delete => ActionType.Ignore
  | ByteClassF.Final =>
      match s with
      | ParserState.CsiEntry | ParserState.CsiParam | ParserState.CsiIntermediate =>
          ActionType.CsiDispatch
      | _ => ActionType.Execute

/-- The concrete transition WITH its emitted action.
  • `Esc`/`Final` clear params, intermediates, and the accumulator;
  • `Param` (a digit) accumulates `curParam` (saturating at `maxParamVal`);
  • `Separator` commits: grows `paramCount` (capped) and resets `curParam`;
  • `Intermediate` grows `interCount` (capped);
  • `C0ctrl`/`Delete` leave the buffers untouched. -/
def stepF (c : ConfigF) (bc : ByteClassF) : ConfigF × ActionType :=
  let cfg :=
    match bc with
    | ByteClassF.Esc =>
        { c with state := ParserState.Escape,
                 paramCount := 0, interCount := 0, curParam := 0 }
    | ByteClassF.Final =>
        { c with state := ParserState.Ground,
                 paramCount := 0, interCount := 0, curParam := 0 }
    | ByteClassF.Param =>
        { c with state := ParserState.CsiParam,
                 curParam := gincr c.curParam maxParamVal }
    | ByteClassF.Separator =>
        { c with state := ParserState.CsiParam,
                 paramCount := gincr c.paramCount maxParams, curParam := 0 }
    | ByteClassF.Intermediate =>
        { c with state := ParserState.CsiIntermediate,
                 interCount := gincr c.interCount maxIntermediates }
    | ByteClassF.C0ctrl => c
    | ByteClassF.Delete => c
  (cfg, actionOf c.state bc)

/-- The ABSTRACT transition with its emitted action, over the abstract state alone
(it has no access to the forgotten sub-state — same shape as `stepF` on the
retained fields). -/
def stepAF (m : ParserModelF) (bc : ByteClassF) : ParserModelF × ActionType :=
  let nm :=
    match bc with
    | ByteClassF.Esc =>
        { m with state := ParserState.Escape,
                 paramCount := 0, interCount := 0, curParam := 0 }
    | ByteClassF.Final =>
        { m with state := ParserState.Ground,
                 paramCount := 0, interCount := 0, curParam := 0 }
    | ByteClassF.Param =>
        { m with state := ParserState.CsiParam,
                 curParam := gincr m.curParam maxParamVal }
    | ByteClassF.Separator =>
        { m with state := ParserState.CsiParam,
                 paramCount := gincr m.paramCount maxParams, curParam := 0 }
    | ByteClassF.Intermediate =>
        { m with state := ParserState.CsiIntermediate,
                 interCount := gincr m.interCount maxIntermediates }
    | ByteClassF.C0ctrl => m
    | ByteClassF.Delete => m
  (nm, actionOf m.state bc)

/-- `projectF` lifted to the `(state, action)` pair: abstract the config, pass the
emitted action through unchanged. -/
def projectF2 (p : ConfigF × ActionType) : ParserModelF × ActionType :=
  (projectF p.1, p.2)

/-- **THEOREM A⁺ — the full invariant is preserved over all inputs.**
`InvF` (now including `CurrentParamBounded`) is closed under `stepF` for every byte
class. The accumulator bound rides on the same `gincr_le` as the buffer bounds. -/
theorem stepF_preserves_invF (c : ConfigF) (bc : ByteClassF) (h : InvF c) :
    InvF (stepF c bc).fst := by
  obtain ⟨hp, hi, hc, hu1, hu2, hda⟩ := h
  cases bc
  case C0ctrl => exact ⟨hp, hi, hc, hu1, hu2, hda⟩
  case Esc => exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, hu1, hu2, hda⟩
  case Intermediate => exact ⟨hp, gincr_le _ _, hc, hu1, hu2, hda⟩
  case Param => exact ⟨hp, hi, gincr_le _ _, hu1, hu2, hda⟩
  case Separator => exact ⟨gincr_le _ _, hi, Nat.zero_le _, hu1, hu2, hda⟩
  case Final => exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, hu1, hu2, hda⟩
  case Delete => exact ⟨hp, hi, hc, hu1, hu2, hda⟩

/-- **THEOREM B⁺ — the COMPLETE refinement square (all four §5.1 CheckKinds).**
Abstracting-then-stepping equals stepping-then-abstracting, INCLUDING the emitted
action, for every config and byte class:
  • `state` agreement   — `CheckKind::ControlFlow`;
  • `paramCount`/`interCount`/`curParam` agreement — `CheckKind::DataFlow`
    (now matching aterm's `ParserModel` field-for-field);
  • emitted `ActionType` agreement — `CheckKind::ReturnValue` (the action edge,
    state-dependent hence non-trivial);
  • `CheckKind::Termination` — trivial (`stepF`/`stepAF` total). -/
theorem parser_refines_model_full (c : ConfigF) (bc : ByteClassF) :
    projectF2 (stepF c bc) = stepAF (projectF c) bc := by
  cases bc <;> rfl

/-! ## Trust-base check — axiom closure must be foundational-only (here: none). -/

#print axioms stepF_preserves_invF
#print axioms parser_refines_model_full

end Crownproof.ATermParserPhase1.Full
