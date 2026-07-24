-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for incremental SAT assumption-stack
-- soundness. Assumption scopes, learned clauses, and formulas are represented
-- propositionally; push/pop and preprocessing transport are explicit
-- forward/backward maps.

def AyIncDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyIncConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyIncEquisat (before : Prop) (after : Prop) :=
  AyIncConj (before -> after) (after -> before)

def AyIncAssumptionStack (active : Prop) (pushed : Prop) :=
  AyIncConj active pushed

def AyIncState (formula : Prop) (learned : Prop) (assumptions : Prop) :=
  AyIncConj formula (AyIncConj learned assumptions)

def AyIncConflictWitness (formula : Prop) (assumptions : Prop) :=
  formula -> assumptions -> False

def AyIncCoreCertificate
    (formula : Prop) (activeAssumptions : Prop) (coreAssumptions : Prop) :=
  AyIncConj
    (activeAssumptions -> coreAssumptions)
    (AyIncConflictWitness formula coreAssumptions)

def AyIncPreprocessMap (original : Prop) (preprocessed : Prop) :=
  AyIncEquisat original preprocessed

theorem ay_inc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyIncConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_inc_conj_left
    (left : Prop) (right : Prop) :
    AyIncConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_inc_conj_right
    (left : Prop) (right : Prop) :
    AyIncConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_inc_equisat_forward
    (before : Prop) (after : Prop) :
    AyIncEquisat before after -> before -> after := by
  intro eqsat
  exact eqsat (before -> after)
    (fun forward _backward => forward)

theorem ay_inc_equisat_backward
    (before : Prop) (after : Prop) :
    AyIncEquisat before after -> after -> before := by
  intro eqsat
  exact eqsat (after -> before)
    (fun _forward backward => backward)

theorem ay_inc_equisat_refl
    (state : Prop) :
    AyIncEquisat state state := by
  exact ay_inc_conj_intro
    (state -> state)
    (state -> state)
    (fun hstate => hstate)
    (fun hstate => hstate)

theorem ay_inc_equisat_trans
    (stage0 : Prop) (stage1 : Prop) (stage2 : Prop) :
    AyIncEquisat stage0 stage1 ->
    AyIncEquisat stage1 stage2 ->
    AyIncEquisat stage0 stage2 :=
  fun first second result build =>
    first result
      (fun firstForward firstBackward =>
        second result
          (fun secondForward secondBackward =>
            build
              (fun h0 => secondForward (firstForward h0))
              (fun h2 => firstBackward (secondBackward h2))))

theorem ay_inc_push_assumption_intro
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AyIncAssumptionStack active pushed := by
  intro hactive
  intro hpushed
  exact ay_inc_conj_intro active pushed hactive hpushed

theorem ay_inc_pop_assumption_projection
    (active : Prop) (pushed : Prop) :
    AyIncAssumptionStack active pushed -> active := by
  intro stack
  exact ay_inc_conj_left active pushed stack

theorem ay_inc_push_pop_equisat
    (active : Prop) (pushed : Prop) :
    (active -> pushed) ->
    AyIncEquisat (AyIncAssumptionStack active pushed) active := by
  intro reconstruct_pushed
  exact ay_inc_conj_intro
    (AyIncAssumptionStack active pushed -> active)
    (active -> AyIncAssumptionStack active pushed)
    (ay_inc_pop_assumption_projection active pushed)
    (fun hactive =>
      ay_inc_push_assumption_intro active pushed
        hactive
        (reconstruct_pushed hactive))

theorem ay_inc_state_push_assumption
    (formula : Prop) (learned : Prop)
    (activeAssumptions : Prop) (pushedAssumption : Prop) :
    AyIncState formula learned activeAssumptions ->
    pushedAssumption ->
    AyIncState
      formula
      learned
      (AyIncAssumptionStack activeAssumptions pushedAssumption) := by
  intro state
  intro hpushed
  exact ay_inc_conj_intro formula
    (AyIncConj learned
      (AyIncAssumptionStack activeAssumptions pushedAssumption))
    (ay_inc_conj_left formula (AyIncConj learned activeAssumptions) state)
    (ay_inc_conj_intro learned
      (AyIncAssumptionStack activeAssumptions pushedAssumption)
      (ay_inc_conj_left learned activeAssumptions
        (ay_inc_conj_right formula (AyIncConj learned activeAssumptions) state))
      (ay_inc_push_assumption_intro
        activeAssumptions pushedAssumption
        (ay_inc_conj_right learned activeAssumptions
          (ay_inc_conj_right formula
            (AyIncConj learned activeAssumptions)
            state))
        hpushed))

theorem ay_inc_state_pop_assumption
    (formula : Prop) (learned : Prop)
    (activeAssumptions : Prop) (pushedAssumption : Prop) :
    AyIncState
      formula
      learned
      (AyIncAssumptionStack activeAssumptions pushedAssumption) ->
    AyIncState formula learned activeAssumptions := by
  intro state
  exact ay_inc_conj_intro formula (AyIncConj learned activeAssumptions)
    (ay_inc_conj_left formula
      (AyIncConj learned
        (AyIncAssumptionStack activeAssumptions pushedAssumption))
      state)
    (ay_inc_conj_intro learned activeAssumptions
      (ay_inc_conj_left learned
        (AyIncAssumptionStack activeAssumptions pushedAssumption)
        (ay_inc_conj_right formula
          (AyIncConj learned
            (AyIncAssumptionStack activeAssumptions pushedAssumption))
          state))
      (ay_inc_pop_assumption_projection activeAssumptions pushedAssumption
        (ay_inc_conj_right learned
          (AyIncAssumptionStack activeAssumptions pushedAssumption)
          (ay_inc_conj_right formula
            (AyIncConj learned
              (AyIncAssumptionStack activeAssumptions pushedAssumption))
            state))))

theorem ay_inc_learned_preserved_push
    (formula : Prop) (learned : Prop)
    (activeAssumptions : Prop) (pushedAssumption : Prop) :
    AyIncState formula learned activeAssumptions ->
    pushedAssumption ->
    learned := by
  intro state
  intro _hpushed
  exact ay_inc_conj_left learned activeAssumptions
    (ay_inc_conj_right formula
      (AyIncConj learned activeAssumptions)
      state)

theorem ay_inc_learned_preserved_pop
    (formula : Prop) (learned : Prop)
    (activeAssumptions : Prop) (pushedAssumption : Prop) :
    AyIncState
      formula
      learned
      (AyIncAssumptionStack activeAssumptions pushedAssumption) ->
    learned := by
  intro state
  exact ay_inc_conj_left learned
    (AyIncAssumptionStack activeAssumptions pushedAssumption)
    (ay_inc_conj_right formula
      (AyIncConj learned
        (AyIncAssumptionStack activeAssumptions pushedAssumption))
      state)

theorem ay_inc_core_projection
    (formula : Prop) (activeAssumptions : Prop) (coreAssumptions : Prop) :
    AyIncCoreCertificate formula activeAssumptions coreAssumptions ->
    activeAssumptions -> coreAssumptions := by
  intro certificate
  exact ay_inc_conj_left
    (activeAssumptions -> coreAssumptions)
    (AyIncConflictWitness formula coreAssumptions)
    certificate

theorem ay_inc_core_conflict
    (formula : Prop) (activeAssumptions : Prop) (coreAssumptions : Prop) :
    AyIncCoreCertificate formula activeAssumptions coreAssumptions ->
    AyIncConflictWitness formula coreAssumptions := by
  intro certificate
  exact ay_inc_conj_right
    (activeAssumptions -> coreAssumptions)
    (AyIncConflictWitness formula coreAssumptions)
    certificate

theorem ay_inc_unsat_core_to_active_assumptions
    (formula : Prop) (activeAssumptions : Prop) (coreAssumptions : Prop) :
    AyIncCoreCertificate formula activeAssumptions coreAssumptions ->
    AyIncConflictWitness formula activeAssumptions := by
  intro certificate
  intro hformula
  intro hactive
  exact ay_inc_core_conflict
    formula activeAssumptions coreAssumptions certificate
    hformula
    (ay_inc_core_projection
      formula activeAssumptions coreAssumptions certificate hactive)

theorem ay_inc_project_core_from_pushed_scope
    (formula : Prop)
    (activeAssumptions : Prop)
    (pushedAssumption : Prop)
    (coreAssumptions : Prop) :
    AyIncCoreCertificate
      formula
      (AyIncAssumptionStack activeAssumptions pushedAssumption)
      coreAssumptions ->
    AyIncAssumptionStack activeAssumptions pushedAssumption ->
    coreAssumptions := by
  intro certificate
  exact ay_inc_core_projection
    formula
    (AyIncAssumptionStack activeAssumptions pushedAssumption)
    coreAssumptions
    certificate

theorem ay_inc_preprocess_model_transport_forward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (learned : Prop) (assumptions : Prop) :
    AyIncPreprocessMap originalFormula preprocessedFormula ->
    AyIncState originalFormula learned assumptions ->
    AyIncState preprocessedFormula learned assumptions := by
  intro preprocess
  intro state
  exact ay_inc_conj_intro preprocessedFormula
    (AyIncConj learned assumptions)
    (ay_inc_equisat_forward originalFormula preprocessedFormula
      preprocess
      (ay_inc_conj_left originalFormula
        (AyIncConj learned assumptions)
        state))
    (ay_inc_conj_right originalFormula
      (AyIncConj learned assumptions)
      state)

theorem ay_inc_preprocess_model_transport_backward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (learned : Prop) (assumptions : Prop) :
    AyIncPreprocessMap originalFormula preprocessedFormula ->
    AyIncState preprocessedFormula learned assumptions ->
    AyIncState originalFormula learned assumptions := by
  intro preprocess
  intro state
  exact ay_inc_conj_intro originalFormula
    (AyIncConj learned assumptions)
    (ay_inc_equisat_backward originalFormula preprocessedFormula
      preprocess
      (ay_inc_conj_left preprocessedFormula
        (AyIncConj learned assumptions)
        state))
    (ay_inc_conj_right preprocessedFormula
      (AyIncConj learned assumptions)
      state)

theorem ay_inc_preprocess_state_equisat
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (learned : Prop) (assumptions : Prop) :
    AyIncPreprocessMap originalFormula preprocessedFormula ->
    AyIncEquisat
      (AyIncState originalFormula learned assumptions)
      (AyIncState preprocessedFormula learned assumptions) := by
  intro preprocess
  exact ay_inc_conj_intro
    (AyIncState originalFormula learned assumptions ->
      AyIncState preprocessedFormula learned assumptions)
    (AyIncState preprocessedFormula learned assumptions ->
      AyIncState originalFormula learned assumptions)
    (ay_inc_preprocess_model_transport_forward
      originalFormula preprocessedFormula learned assumptions preprocess)
    (ay_inc_preprocess_model_transport_backward
      originalFormula preprocessedFormula learned assumptions preprocess)

theorem ay_inc_conflict_transport_preprocess
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (assumptions : Prop) :
    AyIncPreprocessMap originalFormula preprocessedFormula ->
    AyIncConflictWitness preprocessedFormula assumptions ->
    AyIncConflictWitness originalFormula assumptions := by
  intro preprocess
  intro pre_conflict
  intro horiginal
  intro hassumptions
  exact pre_conflict
    (ay_inc_equisat_forward originalFormula preprocessedFormula
      preprocess horiginal)
    hassumptions

theorem ay_inc_push_preprocess_pop_reconstruct
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (learned : Prop) (activeAssumptions : Prop) (pushedAssumption : Prop) :
    AyIncPreprocessMap originalFormula preprocessedFormula ->
    AyIncState
      preprocessedFormula
      learned
      (AyIncAssumptionStack activeAssumptions pushedAssumption) ->
    AyIncState originalFormula learned activeAssumptions := by
  intro preprocess
  intro scoped_state
  exact ay_inc_preprocess_model_transport_backward
    originalFormula
    preprocessedFormula
    learned
    activeAssumptions
    preprocess
    (ay_inc_state_pop_assumption
      preprocessedFormula learned activeAssumptions pushedAssumption
      scoped_state)
