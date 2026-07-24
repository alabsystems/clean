-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked propositional skeleton for LRAT hint minimization interacting with
-- trace splicing. If each trace step remains sound after redundant hints are
-- removed, the minimized steps splice exactly like the original steps.

def AyHintSpliceConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyHintSpliceStep (hints : Prop) (derived : Prop) :=
  hints -> derived

def AyHintSpliceRedundantHint (keptHints : Prop) (redundantHint : Prop) :=
  keptHints -> redundantHint

def AyHintSpliceWithRedundantHint
    (keptHints : Prop) (redundantHint : Prop) :=
  AyHintSpliceConj keptHints redundantHint

def AyHintSpliceWithDerived (available : Prop) (derived : Prop) :=
  AyHintSpliceConj available derived

def AyHintSpliceFirstOriginalHints
    (baseHints : Prop) (firstRedundant : Prop) :=
  AyHintSpliceWithRedundantHint baseHints firstRedundant

def AyHintSpliceSecondOriginalHints
    (baseHints : Prop) (intermediate : Prop) (secondRedundant : Prop) :=
  AyHintSpliceWithRedundantHint
    (AyHintSpliceWithDerived baseHints intermediate)
    secondRedundant

theorem ay_hint_splice_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyHintSpliceConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_hint_splice_conj_left
    (left : Prop) (right : Prop) :
    AyHintSpliceConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_hint_splice_conj_right
    (left : Prop) (right : Prop) :
    AyHintSpliceConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_hint_splice_reconstruct_hint
    (keptHints : Prop) (redundantHint : Prop) :
    AyHintSpliceRedundantHint keptHints redundantHint ->
    keptHints ->
    AyHintSpliceWithRedundantHint keptHints redundantHint := by
  intro redundancy
  intro kept
  exact ay_hint_splice_conj_intro keptHints redundantHint
    kept
    (redundancy kept)

theorem ay_hint_splice_minimize_step
    (keptHints : Prop) (redundantHint : Prop) (derived : Prop) :
    AyHintSpliceRedundantHint keptHints redundantHint ->
    AyHintSpliceStep
      (AyHintSpliceWithRedundantHint keptHints redundantHint)
      derived ->
    AyHintSpliceStep keptHints derived := by
  intro redundancy
  intro originalStep
  intro kept
  exact originalStep
    (ay_hint_splice_reconstruct_hint keptHints redundantHint redundancy kept)

theorem ay_hint_splice_matching_steps
    (baseHints : Prop) (intermediate : Prop) (final : Prop) :
    AyHintSpliceStep baseHints intermediate ->
    AyHintSpliceStep
      (AyHintSpliceWithDerived baseHints intermediate)
      final ->
    AyHintSpliceStep baseHints final := by
  intro firstStep
  intro secondStep
  intro base
  exact secondStep
    (ay_hint_splice_conj_intro baseHints intermediate
      base
      (firstStep base))

theorem ay_hint_splice_minimized_first_step
    (baseHints : Prop) (firstRedundant : Prop) (intermediate : Prop) :
    AyHintSpliceRedundantHint baseHints firstRedundant ->
    AyHintSpliceStep
      (AyHintSpliceFirstOriginalHints baseHints firstRedundant)
      intermediate ->
    AyHintSpliceStep baseHints intermediate := by
  intro redundancy
  intro originalFirst
  exact ay_hint_splice_minimize_step
    baseHints firstRedundant intermediate redundancy originalFirst

theorem ay_hint_splice_minimized_second_step
    (baseHints : Prop)
    (intermediate : Prop)
    (secondRedundant : Prop)
    (final : Prop) :
    AyHintSpliceRedundantHint
      (AyHintSpliceWithDerived baseHints intermediate)
      secondRedundant ->
    AyHintSpliceStep
      (AyHintSpliceSecondOriginalHints
        baseHints intermediate secondRedundant)
      final ->
    AyHintSpliceStep
      (AyHintSpliceWithDerived baseHints intermediate)
      final := by
  intro redundancy
  intro originalSecond
  exact ay_hint_splice_minimize_step
    (AyHintSpliceWithDerived baseHints intermediate)
    secondRedundant
    final
    redundancy
    originalSecond

theorem ay_hint_splice_minimized_steps_splice
    (baseHints : Prop)
    (firstRedundant : Prop)
    (intermediate : Prop)
    (secondRedundant : Prop)
    (final : Prop) :
    AyHintSpliceRedundantHint baseHints firstRedundant ->
    AyHintSpliceRedundantHint
      (AyHintSpliceWithDerived baseHints intermediate)
      secondRedundant ->
    AyHintSpliceStep
      (AyHintSpliceFirstOriginalHints baseHints firstRedundant)
      intermediate ->
    AyHintSpliceStep
      (AyHintSpliceSecondOriginalHints
        baseHints intermediate secondRedundant)
      final ->
    AyHintSpliceStep baseHints final := by
  intro firstRedundancy
  intro secondRedundancy
  intro originalFirst
  intro originalSecond
  exact ay_hint_splice_matching_steps baseHints intermediate final
    (ay_hint_splice_minimized_first_step
      baseHints firstRedundant intermediate
      firstRedundancy
      originalFirst)
    (ay_hint_splice_minimized_second_step
      baseHints intermediate secondRedundant final
      secondRedundancy
      originalSecond)

theorem ay_hint_splice_minimized_steps_at_hints
    (baseHints : Prop)
    (firstRedundant : Prop)
    (intermediate : Prop)
    (secondRedundant : Prop)
    (final : Prop) :
    AyHintSpliceRedundantHint baseHints firstRedundant ->
    AyHintSpliceRedundantHint
      (AyHintSpliceWithDerived baseHints intermediate)
      secondRedundant ->
    AyHintSpliceStep
      (AyHintSpliceFirstOriginalHints baseHints firstRedundant)
      intermediate ->
    AyHintSpliceStep
      (AyHintSpliceSecondOriginalHints
        baseHints intermediate secondRedundant)
      final ->
    baseHints ->
    final := by
  intro firstRedundancy
  intro secondRedundancy
  intro originalFirst
  intro originalSecond
  exact ay_hint_splice_minimized_steps_splice
    baseHints firstRedundant intermediate secondRedundant final
    firstRedundancy
    secondRedundancy
    originalFirst
    originalSecond

theorem ay_hint_splice_preserves_intermediate
    (baseHints : Prop)
    (firstRedundant : Prop)
    (intermediate : Prop) :
    AyHintSpliceRedundantHint baseHints firstRedundant ->
    AyHintSpliceStep
      (AyHintSpliceFirstOriginalHints baseHints firstRedundant)
      intermediate ->
    baseHints ->
    AyHintSpliceWithDerived baseHints intermediate := by
  intro redundancy
  intro originalFirst
  intro base
  exact ay_hint_splice_conj_intro baseHints intermediate
    base
    (ay_hint_splice_minimized_first_step
      baseHints firstRedundant intermediate
      redundancy
      originalFirst
      base)

