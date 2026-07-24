-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorems for repeated inprocessing/restart pipeline soundness.
-- A phase is abstracted as forward/backward maps between satisfiability
-- witnesses. Restart/trail reset preserves the formula state and learned
-- clauses, while final reconstruction is the composed backward map.

def AyRestartDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyRestartConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyRestartEquisat (before : Prop) (after : Prop) :=
  AyRestartConj (before -> after) (after -> before)

def AyRestartTransform (before : Prop) (after : Prop) :=
  AyRestartEquisat before after

def AyRestartState (formula : Prop) (learned : Prop) :=
  AyRestartConj formula learned

def AyRestartPhase (before : Prop) (after : Prop) :=
  AyRestartTransform before after

def AyRestartReset (before : Prop) (after : Prop) :=
  AyRestartTransform before after

def AyRestartVisibleModel (original : Prop) (visible : Prop) :=
  visible -> original

theorem ay_restart_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyRestartConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_restart_conj_left
    (left : Prop) (right : Prop) :
    AyRestartConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_restart_conj_right
    (left : Prop) (right : Prop) :
    AyRestartConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_restart_transform_forward
    (before : Prop) (after : Prop) :
    AyRestartTransform before after -> before -> after := by
  intro transform
  exact transform (before -> after)
    (fun forward _backward => forward)

theorem ay_restart_transform_backward
    (before : Prop) (after : Prop) :
    AyRestartTransform before after -> after -> before := by
  intro transform
  exact transform (after -> before)
    (fun _forward backward => backward)

theorem ay_restart_transform_refl
    (state : Prop) :
    AyRestartTransform state state := by
  exact ay_restart_conj_intro
    (state -> state)
    (state -> state)
    (fun hstate => hstate)
    (fun hstate => hstate)

theorem ay_restart_transform_compose
    (stage0 : Prop) (stage1 : Prop) (stage2 : Prop) :
    AyRestartTransform stage0 stage1 ->
    AyRestartTransform stage1 stage2 ->
    AyRestartTransform stage0 stage2 :=
  fun first second result build =>
    first result
      (fun firstForward firstBackward =>
        second result
          (fun secondForward secondBackward =>
            build
              (fun h0 => secondForward (firstForward h0))
              (fun h2 => firstBackward (secondBackward h2))))

theorem ay_restart_state_map
    (formulaBefore : Prop) (formulaAfter : Prop) (learned : Prop) :
    AyRestartTransform formulaBefore formulaAfter ->
    AyRestartTransform
      (AyRestartState formulaBefore learned)
      (AyRestartState formulaAfter learned) := by
  intro formula_transform
  exact ay_restart_conj_intro
    (AyRestartState formulaBefore learned ->
      AyRestartState formulaAfter learned)
    (AyRestartState formulaAfter learned ->
      AyRestartState formulaBefore learned)
    (fun before_state =>
      ay_restart_conj_intro formulaAfter learned
        (ay_restart_transform_forward
          formulaBefore formulaAfter formula_transform
          (ay_restart_conj_left formulaBefore learned before_state))
        (ay_restart_conj_right formulaBefore learned before_state))
    (fun after_state =>
      ay_restart_conj_intro formulaBefore learned
        (ay_restart_transform_backward
          formulaBefore formulaAfter formula_transform
          (ay_restart_conj_left formulaAfter learned after_state))
        (ay_restart_conj_right formulaAfter learned after_state))

theorem ay_restart_trail_reset_preserves_state
    (formula : Prop) (learned : Prop) :
    AyRestartReset
      (AyRestartState formula learned)
      (AyRestartState formula learned) := by
  exact ay_restart_transform_refl (AyRestartState formula learned)

theorem ay_restart_preserves_learned_forward
    (formulaBefore : Prop) (formulaAfter : Prop) (learned : Prop) :
    AyRestartTransform formulaBefore formulaAfter ->
    AyRestartState formulaBefore learned ->
    learned := by
  intro _formula_transform
  intro before_state
  exact ay_restart_conj_right formulaBefore learned before_state

theorem ay_restart_preserves_learned_backward
    (formulaBefore : Prop) (formulaAfter : Prop) (learned : Prop) :
    AyRestartTransform formulaBefore formulaAfter ->
    AyRestartState formulaAfter learned ->
    learned := by
  intro _formula_transform
  intro after_state
  exact ay_restart_conj_right formulaAfter learned after_state

theorem ay_restart_two_phase_pipeline
    (stage0 : Prop) (stage1 : Prop) (stage2 : Prop) (stage3 : Prop) :
    AyRestartPhase stage0 stage1 ->
    AyRestartReset stage1 stage2 ->
    AyRestartPhase stage2 stage3 ->
    AyRestartTransform stage0 stage3 := by
  intro first_phase
  intro reset
  intro second_phase
  exact ay_restart_transform_compose stage0 stage2 stage3
    (ay_restart_transform_compose stage0 stage1 stage2
      first_phase
      reset)
    second_phase

theorem ay_restart_three_phase_pipeline
    (stage0 : Prop) (stage1 : Prop) (stage2 : Prop)
    (stage3 : Prop) (stage4 : Prop) (stage5 : Prop) :
    AyRestartPhase stage0 stage1 ->
    AyRestartReset stage1 stage2 ->
    AyRestartPhase stage2 stage3 ->
    AyRestartReset stage3 stage4 ->
    AyRestartPhase stage4 stage5 ->
    AyRestartTransform stage0 stage5 := by
  intro phase1
  intro reset1
  intro phase2
  intro reset2
  intro phase3
  exact ay_restart_transform_compose stage0 stage3 stage5
    (ay_restart_two_phase_pipeline
      stage0 stage1 stage2 stage3
      phase1 reset1 phase2)
    (ay_restart_transform_compose stage3 stage4 stage5
      reset2 phase3)

theorem ay_restart_state_two_inprocessing_rounds
    (formula0 : Prop) (formula1 : Prop) (formula2 : Prop)
    (learned : Prop) :
    AyRestartTransform formula0 formula1 ->
    AyRestartTransform formula1 formula2 ->
    AyRestartTransform
      (AyRestartState formula0 learned)
      (AyRestartState formula2 learned) := by
  intro first_round
  intro second_round
  exact ay_restart_transform_compose
    (AyRestartState formula0 learned)
    (AyRestartState formula1 learned)
    (AyRestartState formula2 learned)
    (ay_restart_state_map formula0 formula1 learned first_round)
    (ay_restart_state_map formula1 formula2 learned second_round)

theorem ay_restart_state_rounds_with_reset
    (formula0 : Prop) (formula1 : Prop) (formula2 : Prop)
    (learned : Prop) :
    AyRestartTransform formula0 formula1 ->
    AyRestartReset
      (AyRestartState formula1 learned)
      (AyRestartState formula1 learned) ->
    AyRestartTransform formula1 formula2 ->
    AyRestartTransform
      (AyRestartState formula0 learned)
      (AyRestartState formula2 learned) := by
  intro first_round
  intro reset
  intro second_round
  exact ay_restart_transform_compose
    (AyRestartState formula0 learned)
    (AyRestartState formula1 learned)
    (AyRestartState formula2 learned)
    (ay_restart_transform_compose
      (AyRestartState formula0 learned)
      (AyRestartState formula1 learned)
      (AyRestartState formula1 learned)
      (ay_restart_state_map formula0 formula1 learned first_round)
      reset)
    (ay_restart_state_map formula1 formula2 learned second_round)

theorem ay_restart_final_visible_model_reconstruction
    (originalFormula : Prop) (finalFormula : Prop) (learned : Prop) :
    AyRestartTransform originalFormula finalFormula ->
    AyRestartVisibleModel
      originalFormula
      (AyRestartState finalFormula learned) := by
  intro pipeline
  intro final_state
  exact ay_restart_transform_backward
    originalFormula
    finalFormula
    pipeline
    (ay_restart_conj_left finalFormula learned final_state)

theorem ay_restart_final_visible_state_reconstruction
    (originalFormula : Prop) (finalFormula : Prop) (learned : Prop) :
    AyRestartTransform
      (AyRestartState originalFormula learned)
      (AyRestartState finalFormula learned) ->
    AyRestartState finalFormula learned ->
    AyRestartState originalFormula learned := by
  intro pipeline
  intro final_state
  exact ay_restart_transform_backward
    (AyRestartState originalFormula learned)
    (AyRestartState finalFormula learned)
    pipeline
    final_state

theorem ay_restart_visible_model_after_two_rounds
    (originalFormula : Prop) (formula1 : Prop) (finalFormula : Prop)
    (learned : Prop) :
    AyRestartTransform originalFormula formula1 ->
    AyRestartTransform formula1 finalFormula ->
    AyRestartVisibleModel
      originalFormula
      (AyRestartState finalFormula learned) := by
  intro first_round
  intro second_round
  exact ay_restart_final_visible_model_reconstruction
    originalFormula
    finalFormula
    learned
    (ay_restart_transform_compose
      originalFormula formula1 finalFormula first_round second_round)

theorem ay_restart_pipeline_preserves_sat_interface
    (originalFormula : Prop) (formula1 : Prop) (finalFormula : Prop)
    (learned : Prop) :
    AyRestartTransform originalFormula formula1 ->
    AyRestartTransform formula1 finalFormula ->
    AyRestartEquisat
      (AyRestartState originalFormula learned)
      (AyRestartState finalFormula learned) := by
  intro first_round
  intro second_round
  exact ay_restart_state_two_inprocessing_rounds
    originalFormula formula1 finalFormula learned
    first_round second_round
