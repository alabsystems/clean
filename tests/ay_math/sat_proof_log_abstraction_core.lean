-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for proof-log abstraction and replay.
-- RAT/LRAT steps are abstract soundness implications from an available
-- clause database/log state to a derived clause. Compression removes
-- intermediate proof-log states while preserving the final derived clause.

def AyLogConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyLogDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyLogEquisat (before : Prop) (after : Prop) :=
  AyLogConj (before -> after) (after -> before)

def AyLogStep (available : Prop) (derived : Prop) :=
  available -> derived

def AyRatLogStep (available : Prop) (derived : Prop) :=
  AyLogStep available derived

def AyLratLogStep (available : Prop) (derived : Prop) :=
  AyLogStep available derived

def AyLogWithClause (database : Prop) (clause : Prop) :=
  AyLogConj database clause

def AyLogTwoStepState
    (database : Prop) (intermediate : Prop) (final : Prop) :=
  AyLogConj database (AyLogConj intermediate final)

def AyAbstractLogState
    (database : Prop) (final : Prop) :=
  AyLogConj database final

def AyConcreteReplay
    (concreteDatabase : Prop) (abstractState : Prop) :=
  concreteDatabase -> abstractState

theorem ay_log_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyLogConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_log_conj_left
    (left : Prop) (right : Prop) :
    AyLogConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_log_conj_right
    (left : Prop) (right : Prop) :
    AyLogConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_log_disj_left
    (left : Prop) (right : Prop) :
    left -> AyLogDisj left right := by
  intro hleft
  intro result
  intro leftCase
  intro _rightCase
  exact leftCase hleft

theorem ay_log_disj_right
    (left : Prop) (right : Prop) :
    right -> AyLogDisj left right := by
  intro hright
  intro result
  intro _leftCase
  intro rightCase
  exact rightCase hright

theorem ay_log_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyLogEquisat before after :=
  fun forward backward result keep =>
    keep forward backward

theorem ay_log_equisat_forward
    (before : Prop) (after : Prop) :
    AyLogEquisat before after -> before -> after :=
  fun equisat =>
    equisat (before -> after)
      (fun forward _backward => forward)

theorem ay_log_equisat_backward
    (before : Prop) (after : Prop) :
    AyLogEquisat before after -> after -> before :=
  fun equisat =>
    equisat (after -> before)
      (fun _forward backward => backward)

theorem ay_log_step_compose
    (available : Prop) (intermediate : Prop) (final : Prop) :
    AyLogStep available intermediate ->
    AyLogStep intermediate final ->
    AyLogStep available final :=
  fun firstStep secondStep availableH =>
    secondStep (firstStep availableH)

theorem ay_rat_lrat_step_compose
    (available : Prop) (intermediate : Prop) (final : Prop) :
    AyRatLogStep available intermediate ->
    AyLratLogStep intermediate final ->
    AyLogStep available final :=
  fun ratStep lratStep =>
    ay_log_step_compose available intermediate final ratStep lratStep

theorem ay_lrat_rat_step_compose
    (available : Prop) (intermediate : Prop) (final : Prop) :
    AyLratLogStep available intermediate ->
    AyRatLogStep intermediate final ->
    AyLogStep available final :=
  fun lratStep ratStep =>
    ay_log_step_compose available intermediate final lratStep ratStep

theorem ay_log_add_derived_projection
    (database : Prop) (derived : Prop) :
    AyLogWithClause database derived -> database :=
  fun withClause =>
    ay_log_conj_left database derived withClause

theorem ay_log_add_derived_reconstruction
    (database : Prop) (derived : Prop) :
    AyLogStep database derived ->
    database ->
    AyLogWithClause database derived :=
  fun step databaseH =>
    ay_log_conj_intro database derived databaseH (step databaseH)

theorem ay_log_add_derived_equisat
    (database : Prop) (derived : Prop) :
    AyLogStep database derived ->
    AyLogEquisat database (AyLogWithClause database derived) :=
  fun step =>
    ay_log_equisat_intro database
      (AyLogWithClause database derived)
      (ay_log_add_derived_reconstruction database derived step)
      (ay_log_add_derived_projection database derived)

theorem ay_log_two_step_expand
    (database : Prop) (intermediate : Prop) (final : Prop) :
    AyLogStep database intermediate ->
    (AyLogWithClause database intermediate -> final) ->
    database ->
    AyLogTwoStepState database intermediate final :=
  fun firstStep secondStep databaseH =>
    ay_log_conj_intro database
      (AyLogConj intermediate final)
      databaseH
      (ay_log_conj_intro intermediate final
        (firstStep databaseH)
        (secondStep
          (ay_log_conj_intro database intermediate
            databaseH
            (firstStep databaseH))))

theorem ay_log_two_step_final_sound
    (database : Prop) (intermediate : Prop) (final : Prop) :
    AyLogTwoStepState database intermediate final ->
    final :=
  fun state =>
    ay_log_conj_right intermediate final
      (ay_log_conj_right database
        (AyLogConj intermediate final)
        state)

theorem ay_log_compress_two_steps
    (database : Prop) (intermediate : Prop) (final : Prop) :
    AyLogStep database intermediate ->
    (AyLogWithClause database intermediate -> final) ->
    AyLogStep database final :=
  fun firstStep secondStep databaseH =>
    ay_log_two_step_final_sound database intermediate final
      (ay_log_two_step_expand
        database intermediate final firstStep secondStep databaseH)

theorem ay_log_compress_rat_lrat
    (database : Prop) (intermediate : Prop) (final : Prop) :
    AyRatLogStep database intermediate ->
    (AyLogWithClause database intermediate -> final) ->
    AyLogStep database final :=
  fun ratStep lratStep =>
    ay_log_compress_two_steps database intermediate final
      ratStep lratStep

theorem ay_log_compress_lrat_rat
    (database : Prop) (intermediate : Prop) (final : Prop) :
    AyLratLogStep database intermediate ->
    (AyLogWithClause database intermediate -> final) ->
    AyLogStep database final :=
  fun lratStep ratStep =>
    ay_log_compress_two_steps database intermediate final
      lratStep ratStep

theorem ay_log_compressed_preserves_final_clause
    (database : Prop) (intermediate : Prop) (final : Prop) :
    AyLogStep database intermediate ->
    (AyLogWithClause database intermediate -> final) ->
    database ->
    final :=
  fun firstStep secondStep databaseH =>
    ay_log_compress_two_steps
      database intermediate final firstStep secondStep databaseH

theorem ay_log_compress_projection
    (database : Prop) (intermediate : Prop) (final : Prop) :
    AyLogTwoStepState database intermediate final ->
    AyAbstractLogState database final :=
  fun expanded =>
    ay_log_conj_intro database final
      (ay_log_conj_left database
        (AyLogConj intermediate final)
        expanded)
      (ay_log_two_step_final_sound
        database intermediate final expanded)

theorem ay_log_compress_reconstruction
    (database : Prop) (intermediate : Prop) (final : Prop) :
    AyLogStep database intermediate ->
    AyAbstractLogState database final ->
    AyLogTwoStepState database intermediate final :=
  fun firstStep abstractState =>
    abstractState (AyLogTwoStepState database intermediate final)
      (fun databaseH finalH =>
        ay_log_conj_intro database
          (AyLogConj intermediate final)
          databaseH
          (ay_log_conj_intro intermediate final
            (firstStep databaseH)
            finalH))

theorem ay_log_compression_equisat
    (database : Prop) (intermediate : Prop) (final : Prop) :
    AyLogStep database intermediate ->
    AyLogEquisat
      (AyLogTwoStepState database intermediate final)
      (AyAbstractLogState database final) :=
  fun firstStep =>
    ay_log_equisat_intro
      (AyLogTwoStepState database intermediate final)
      (AyAbstractLogState database final)
      (ay_log_compress_projection database intermediate final)
      (ay_log_compress_reconstruction
        database intermediate final firstStep)

theorem ay_log_replay_abstract_against_concrete
    (concreteDatabase : Prop) (abstractDatabase : Prop) (final : Prop) :
    AyConcreteReplay concreteDatabase abstractDatabase ->
    AyLogStep abstractDatabase final ->
    concreteDatabase ->
    AyAbstractLogState concreteDatabase final :=
  fun replay step concreteH =>
    ay_log_conj_intro concreteDatabase final
      concreteH
      (step (replay concreteH))

theorem ay_log_replay_compressed_against_concrete
    (concreteDatabase : Prop) (abstractDatabase : Prop)
    (intermediate : Prop) (final : Prop) :
    AyConcreteReplay concreteDatabase abstractDatabase ->
    AyLogStep abstractDatabase intermediate ->
    (AyLogWithClause abstractDatabase intermediate -> final) ->
    concreteDatabase ->
    AyAbstractLogState concreteDatabase final :=
  fun replay firstStep secondStep concreteH =>
    ay_log_replay_abstract_against_concrete
      concreteDatabase abstractDatabase final
      replay
      (ay_log_compress_two_steps
        abstractDatabase intermediate final firstStep secondStep)
      concreteH

theorem ay_log_replay_preserves_final_clause
    (concreteDatabase : Prop) (abstractDatabase : Prop)
    (final : Prop) :
    AyConcreteReplay concreteDatabase abstractDatabase ->
    AyLogStep abstractDatabase final ->
    concreteDatabase ->
    final :=
  fun replay step concreteH =>
    ay_log_conj_right concreteDatabase final
      (ay_log_replay_abstract_against_concrete
        concreteDatabase abstractDatabase final replay step concreteH)

theorem ay_log_replay_with_compression_preserves_final_clause
    (concreteDatabase : Prop) (abstractDatabase : Prop)
    (intermediate : Prop) (final : Prop) :
    AyConcreteReplay concreteDatabase abstractDatabase ->
    AyLogStep abstractDatabase intermediate ->
    (AyLogWithClause abstractDatabase intermediate -> final) ->
    concreteDatabase ->
    final :=
  fun replay firstStep secondStep concreteH =>
    ay_log_replay_preserves_final_clause
      concreteDatabase abstractDatabase final
      replay
      (ay_log_compress_two_steps
        abstractDatabase intermediate final firstStep secondStep)
      concreteH
