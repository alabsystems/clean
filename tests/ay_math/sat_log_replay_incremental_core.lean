-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for composing proof-log replay with
-- incremental assumptions. Databases, assumptions, models, conflicts, and
-- proof-log states are represented propositionally; all transport is explicit.

def AyLogIncConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyLogIncDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyLogIncEquisat (before : Prop) (after : Prop) :=
  AyLogIncConj (before -> after) (after -> before)

def AyLogIncStep (available : Prop) (derived : Prop) :=
  available -> derived

def AyLogIncReplay (concrete : Prop) (abstract : Prop) :=
  concrete -> abstract

def AyLogIncScope (active : Prop) (pushed : Prop) :=
  AyLogIncConj active pushed

def AyLogIncScopedDb (database : Prop) (assumptions : Prop) :=
  AyLogIncConj database assumptions

def AyLogIncState (formula : Prop) (learned : Prop) (assumptions : Prop) :=
  AyLogIncConj formula (AyLogIncConj learned assumptions)

def AyLogIncCoreCertificate
    (formula : Prop) (activeAssumptions : Prop) (coreAssumptions : Prop) :=
  AyLogIncConj
    (activeAssumptions -> coreAssumptions)
    (formula -> coreAssumptions -> False)

def AyLogIncPreprocessMap (original : Prop) (preprocessed : Prop) :=
  AyLogIncEquisat original preprocessed

theorem ay_log_inc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyLogIncConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_log_inc_conj_left
    (left : Prop) (right : Prop) :
    AyLogIncConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_log_inc_conj_right
    (left : Prop) (right : Prop) :
    AyLogIncConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_log_inc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyLogIncDisj left right := by
  intro hleft
  intro result
  intro leftCase
  intro _rightCase
  exact leftCase hleft

theorem ay_log_inc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyLogIncDisj left right := by
  intro hright
  intro result
  intro _leftCase
  intro rightCase
  exact rightCase hright

theorem ay_log_inc_equisat_forward
    (before : Prop) (after : Prop) :
    AyLogIncEquisat before after -> before -> after :=
  fun equisat =>
    equisat (before -> after)
      (fun forward _backward => forward)

theorem ay_log_inc_equisat_backward
    (before : Prop) (after : Prop) :
    AyLogIncEquisat before after -> after -> before :=
  fun equisat =>
    equisat (after -> before)
      (fun _forward backward => backward)

theorem ay_log_inc_push_scope
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AyLogIncScope active pushed :=
  fun activeH pushedH =>
    ay_log_inc_conj_intro active pushed activeH pushedH

theorem ay_log_inc_pop_scope
    (active : Prop) (pushed : Prop) :
    AyLogIncScope active pushed -> active :=
  fun scoped =>
    scoped active (fun activeH _pushedH => activeH)

theorem ay_log_inc_push_pop_equisat
    (active : Prop) (pushed : Prop) :
    (active -> pushed) ->
    AyLogIncEquisat (AyLogIncScope active pushed) active :=
  fun recoverPushed result keep =>
    keep
      (fun scoped =>
        scoped active (fun activeH _pushedH => activeH))
      (fun activeH =>
        fun result2 build =>
          build activeH (recoverPushed activeH))

theorem ay_log_inc_replay_scoped
    (concreteDb : Prop) (abstractDb : Prop)
    (assumptions : Prop) :
    AyLogIncReplay concreteDb abstractDb ->
    AyLogIncReplay
      (AyLogIncScopedDb concreteDb assumptions)
      (AyLogIncScopedDb abstractDb assumptions) :=
  fun replay scopedConcrete =>
    scopedConcrete (AyLogIncScopedDb abstractDb assumptions)
      (fun concreteH assumptionsH =>
        ay_log_inc_conj_intro abstractDb assumptions
          (replay concreteH)
          assumptionsH)

theorem ay_log_inc_replay_under_push
    (concreteDb : Prop) (abstractDb : Prop)
    (active : Prop) (pushed : Prop) :
    AyLogIncReplay concreteDb abstractDb ->
    AyLogIncReplay
      (AyLogIncScopedDb concreteDb (AyLogIncScope active pushed))
      (AyLogIncScopedDb abstractDb (AyLogIncScope active pushed)) :=
  fun replay =>
    ay_log_inc_replay_scoped
      concreteDb abstractDb (AyLogIncScope active pushed) replay

theorem ay_log_inc_replay_after_pop
    (concreteDb : Prop) (abstractDb : Prop)
    (active : Prop) (pushed : Prop) :
    AyLogIncReplay concreteDb abstractDb ->
    AyLogIncScopedDb concreteDb (AyLogIncScope active pushed) ->
    AyLogIncScopedDb abstractDb active :=
  fun replay scopedConcrete =>
    scopedConcrete (AyLogIncScopedDb abstractDb active)
      (fun concreteH scopedAssumptions =>
        ay_log_inc_conj_intro abstractDb active
          (replay concreteH)
          (scopedAssumptions active
            (fun activeH _pushedH => activeH)))

theorem ay_log_inc_final_clause_replay
    (concreteDb : Prop) (abstractDb : Prop) (finalClause : Prop) :
    AyLogIncReplay concreteDb abstractDb ->
    AyLogIncStep abstractDb finalClause ->
    concreteDb ->
    finalClause :=
  fun replay step concreteH =>
    step (replay concreteH)

theorem ay_log_inc_final_clause_replay_scoped
    (concreteDb : Prop) (abstractDb : Prop)
    (assumptions : Prop) (finalClause : Prop) :
    AyLogIncReplay concreteDb abstractDb ->
    AyLogIncStep
      (AyLogIncScopedDb abstractDb assumptions)
      finalClause ->
    AyLogIncScopedDb concreteDb assumptions ->
    finalClause :=
  fun replay step scopedConcrete =>
    step
      (ay_log_inc_replay_scoped
        concreteDb abstractDb assumptions replay scopedConcrete)

theorem ay_log_inc_final_clause_under_push
    (concreteDb : Prop) (abstractDb : Prop)
    (active : Prop) (pushed : Prop) (finalClause : Prop) :
    AyLogIncReplay concreteDb abstractDb ->
    AyLogIncStep
      (AyLogIncScopedDb abstractDb (AyLogIncScope active pushed))
      finalClause ->
    AyLogIncScopedDb concreteDb (AyLogIncScope active pushed) ->
    finalClause :=
  fun replay step scopedConcrete =>
    ay_log_inc_final_clause_replay_scoped
      concreteDb abstractDb (AyLogIncScope active pushed)
      finalClause replay step scopedConcrete

theorem ay_log_inc_core_projection
    (formula : Prop) (activeAssumptions : Prop) (coreAssumptions : Prop) :
    AyLogIncCoreCertificate formula activeAssumptions coreAssumptions ->
    activeAssumptions -> coreAssumptions :=
  fun certificate =>
    ay_log_inc_conj_left
      (activeAssumptions -> coreAssumptions)
      (formula -> coreAssumptions -> False)
      certificate

theorem ay_log_inc_core_conflict
    (formula : Prop) (activeAssumptions : Prop) (coreAssumptions : Prop) :
    AyLogIncCoreCertificate formula activeAssumptions coreAssumptions ->
    formula -> coreAssumptions -> False :=
  fun certificate =>
    ay_log_inc_conj_right
      (activeAssumptions -> coreAssumptions)
      (formula -> coreAssumptions -> False)
      certificate

theorem ay_log_inc_assumption_core_through_replay
    (concreteDb : Prop) (abstractDb : Prop)
    (activeAssumptions : Prop) (coreAssumptions : Prop) :
    AyLogIncReplay concreteDb abstractDb ->
    AyLogIncCoreCertificate
      abstractDb activeAssumptions coreAssumptions ->
    AyLogIncScopedDb concreteDb activeAssumptions ->
    coreAssumptions :=
  fun _replay certificate scopedConcrete =>
    ay_log_inc_core_projection
      abstractDb activeAssumptions coreAssumptions certificate
      (ay_log_inc_conj_right concreteDb activeAssumptions scopedConcrete)

theorem ay_log_inc_conflict_through_replay
    (concreteDb : Prop) (abstractDb : Prop)
    (activeAssumptions : Prop) (coreAssumptions : Prop) :
    AyLogIncReplay concreteDb abstractDb ->
    AyLogIncCoreCertificate
      abstractDb activeAssumptions coreAssumptions ->
    AyLogIncScopedDb concreteDb activeAssumptions ->
    False :=
  fun replay certificate scopedConcrete =>
    ay_log_inc_core_conflict
      abstractDb activeAssumptions coreAssumptions certificate
      (replay
        (ay_log_inc_conj_left concreteDb activeAssumptions scopedConcrete))
      (ay_log_inc_assumption_core_through_replay
        concreteDb abstractDb activeAssumptions coreAssumptions
        replay certificate scopedConcrete)

theorem ay_log_inc_preprocess_state_forward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (learned : Prop) (assumptions : Prop) :
    AyLogIncPreprocessMap originalFormula preprocessedFormula ->
    AyLogIncState originalFormula learned assumptions ->
    AyLogIncState preprocessedFormula learned assumptions :=
  fun preprocess state =>
    ay_log_inc_conj_intro preprocessedFormula
      (AyLogIncConj learned assumptions)
      (ay_log_inc_equisat_forward
        originalFormula preprocessedFormula preprocess
        (ay_log_inc_conj_left originalFormula
          (AyLogIncConj learned assumptions)
          state))
      (ay_log_inc_conj_right originalFormula
        (AyLogIncConj learned assumptions)
        state)

theorem ay_log_inc_preprocess_state_backward
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (learned : Prop) (assumptions : Prop) :
    AyLogIncPreprocessMap originalFormula preprocessedFormula ->
    AyLogIncState preprocessedFormula learned assumptions ->
    AyLogIncState originalFormula learned assumptions :=
  fun preprocess state =>
    ay_log_inc_conj_intro originalFormula
      (AyLogIncConj learned assumptions)
      (ay_log_inc_equisat_backward
        originalFormula preprocessedFormula preprocess
        (ay_log_inc_conj_left preprocessedFormula
          (AyLogIncConj learned assumptions)
          state))
      (ay_log_inc_conj_right preprocessedFormula
        (AyLogIncConj learned assumptions)
        state)

theorem ay_log_inc_preprocess_model_transport
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (learned : Prop) (assumptions : Prop) :
    AyLogIncPreprocessMap originalFormula preprocessedFormula ->
    AyLogIncEquisat
      (AyLogIncState originalFormula learned assumptions)
      (AyLogIncState preprocessedFormula learned assumptions) :=
  fun preprocess result keep =>
    keep
      (ay_log_inc_preprocess_state_forward
        originalFormula preprocessedFormula learned assumptions preprocess)
      (ay_log_inc_preprocess_state_backward
        originalFormula preprocessedFormula learned assumptions preprocess)

theorem ay_log_inc_conflict_transport_preprocess
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (assumptions : Prop) :
    AyLogIncPreprocessMap originalFormula preprocessedFormula ->
    (preprocessedFormula -> assumptions -> False) ->
    originalFormula -> assumptions -> False :=
  fun preprocess preConflict originalH assumptionsH =>
    preConflict
      (ay_log_inc_equisat_forward
        originalFormula preprocessedFormula preprocess originalH)
      assumptionsH

theorem ay_log_inc_replay_conflict_transport_preprocess
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (abstractDb : Prop) (assumptions : Prop) (coreAssumptions : Prop) :
    AyLogIncPreprocessMap originalFormula preprocessedFormula ->
    AyLogIncReplay preprocessedFormula abstractDb ->
    AyLogIncCoreCertificate abstractDb assumptions coreAssumptions ->
    originalFormula -> assumptions -> False :=
  fun preprocess replay certificate originalH assumptionsH =>
    ay_log_inc_conflict_through_replay
      preprocessedFormula abstractDb assumptions coreAssumptions
      replay
      certificate
      (ay_log_inc_conj_intro preprocessedFormula assumptions
        (ay_log_inc_equisat_forward
          originalFormula preprocessedFormula preprocess originalH)
        assumptionsH)

theorem ay_log_inc_model_reconstruct_after_pop
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (learned : Prop) (active : Prop) (pushed : Prop) :
    AyLogIncPreprocessMap originalFormula preprocessedFormula ->
    AyLogIncState
      preprocessedFormula learned (AyLogIncScope active pushed) ->
    AyLogIncState originalFormula learned active :=
  fun preprocess scopedState =>
    ay_log_inc_preprocess_state_backward
      originalFormula preprocessedFormula learned active preprocess
      (ay_log_inc_conj_intro preprocessedFormula
        (AyLogIncConj learned active)
        (ay_log_inc_conj_left preprocessedFormula
          (AyLogIncConj learned (AyLogIncScope active pushed))
          scopedState)
        (ay_log_inc_conj_intro learned active
          (ay_log_inc_conj_left learned
            (AyLogIncScope active pushed)
            (ay_log_inc_conj_right preprocessedFormula
              (AyLogIncConj learned (AyLogIncScope active pushed))
              scopedState))
          ((ay_log_inc_conj_right learned
            (AyLogIncScope active pushed)
            (ay_log_inc_conj_right preprocessedFormula
              (AyLogIncConj learned (AyLogIncScope active pushed))
              scopedState))
            active
            (fun activeH _pushedH => activeH)))))
