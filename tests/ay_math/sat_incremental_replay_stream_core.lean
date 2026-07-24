-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked core theorem package for incremental assumptions, chunked proof-log
-- replay, and streaming certificates. The propositions represent database,
-- assumption, model, conflict, and chunk states; all maps are explicit.

def AyStreamConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyStreamDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyStreamEquisat (before : Prop) (after : Prop) :=
  AyStreamConj (before -> after) (after -> before)

def AyStreamScope (active : Prop) (pushed : Prop) :=
  forall result : Prop, (active -> pushed -> result) -> result

def AyStreamDb (database : Prop) (assumptions : Prop) :=
  forall result : Prop, (database -> assumptions -> result) -> result

def AyStreamState (database : Prop) (assumptions : Prop) (logState : Prop) :=
  forall result : Prop,
    (AyStreamDb database assumptions -> logState -> result) ->
    result

def AyStreamChunk (before : Prop) (after : Prop) :=
  before -> after

def AyStreamReplay (concrete : Prop) (abstract : Prop) :=
  concrete -> abstract

def AyStreamFinalClause (state : Prop) (finalClause : Prop) :=
  state -> finalClause

def AyStreamCoreCertificate
    (formula : Prop) (activeAssumptions : Prop) (coreAssumptions : Prop) :=
  AyStreamConj
    (activeAssumptions -> coreAssumptions)
    (formula -> coreAssumptions -> False)

def AyStreamPreprocessMap (original : Prop) (preprocessed : Prop) :=
  AyStreamEquisat original preprocessed

theorem ay_stream_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyStreamConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_stream_conj_left
    (left : Prop) (right : Prop) :
    AyStreamConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_stream_conj_right
    (left : Prop) (right : Prop) :
    AyStreamConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_stream_disj_left
    (left : Prop) (right : Prop) :
    left -> AyStreamDisj left right := by
  intro hleft
  intro result
  intro leftCase
  intro _rightCase
  exact leftCase hleft

theorem ay_stream_disj_right
    (left : Prop) (right : Prop) :
    right -> AyStreamDisj left right := by
  intro hright
  intro result
  intro _leftCase
  intro rightCase
  exact rightCase hright

theorem ay_stream_db_intro
    (database : Prop) (assumptions : Prop) :
    database -> assumptions -> AyStreamDb database assumptions :=
  fun databaseH assumptionsH result build =>
    build databaseH assumptionsH

theorem ay_stream_db_left
    (database : Prop) (assumptions : Prop) :
    AyStreamDb database assumptions -> database :=
  fun dbScope =>
    dbScope database (fun databaseH _assumptionsH => databaseH)

theorem ay_stream_db_right
    (database : Prop) (assumptions : Prop) :
    AyStreamDb database assumptions -> assumptions :=
  fun dbScope =>
    dbScope assumptions (fun _databaseH assumptionsH => assumptionsH)

theorem ay_stream_state_intro
    (database : Prop) (assumptions : Prop) (logState : Prop) :
    AyStreamDb database assumptions ->
    logState ->
    AyStreamState database assumptions logState :=
  fun dbScope logH result build =>
    build dbScope logH

theorem ay_stream_state_db
    (database : Prop) (assumptions : Prop) (logState : Prop) :
    AyStreamState database assumptions logState ->
    AyStreamDb database assumptions :=
  fun state =>
    state (AyStreamDb database assumptions)
      (fun dbScope _logH => dbScope)

theorem ay_stream_state_log
    (database : Prop) (assumptions : Prop) (logState : Prop) :
    AyStreamState database assumptions logState ->
    logState :=
  fun state =>
    state logState (fun _dbScope logH => logH)

theorem ay_stream_equisat_forward
    (before : Prop) (after : Prop) :
    AyStreamEquisat before after -> before -> after :=
  fun equisat =>
    equisat (before -> after)
      (fun forward _backward => forward)

theorem ay_stream_equisat_backward
    (before : Prop) (after : Prop) :
    AyStreamEquisat before after -> after -> before :=
  fun equisat =>
    equisat (after -> before)
      (fun _forward backward => backward)

theorem ay_stream_push_scope
    (active : Prop) (pushed : Prop) :
    active -> pushed -> AyStreamScope active pushed :=
  fun activeH pushedH =>
    ay_stream_conj_intro active pushed activeH pushedH

theorem ay_stream_chunk_apply
    (before : Prop) (after : Prop) :
    AyStreamChunk before after -> before -> after :=
  fun chunk beforeH =>
    chunk beforeH

theorem ay_stream_chunk_handoff
    (first : Prop) (middle : Prop) (last : Prop) :
    AyStreamChunk first middle ->
    AyStreamChunk middle last ->
    AyStreamChunk first last :=
  fun firstChunk secondChunk firstH =>
    secondChunk (firstChunk firstH)

theorem ay_stream_chunk_handoff_state
    (database : Prop) (assumptions : Prop)
    (chunkA chunkB chunkC : Prop) :
    AyStreamChunk
      (AyStreamState database assumptions chunkA)
      (AyStreamState database assumptions chunkB) ->
    AyStreamChunk
      (AyStreamState database assumptions chunkB)
      (AyStreamState database assumptions chunkC) ->
    AyStreamChunk
      (AyStreamState database assumptions chunkA)
      (AyStreamState database assumptions chunkC) :=
  fun firstChunk secondChunk =>
    ay_stream_chunk_handoff
      (AyStreamState database assumptions chunkA)
      (AyStreamState database assumptions chunkB)
      (AyStreamState database assumptions chunkC)
      firstChunk
      secondChunk

theorem ay_stream_replay_scoped
    (concreteDb : Prop) (abstractDb : Prop) (assumptions : Prop) :
    AyStreamReplay concreteDb abstractDb ->
    AyStreamReplay
      (AyStreamDb concreteDb assumptions)
      (AyStreamDb abstractDb assumptions) :=
  fun replay scopedConcrete =>
    scopedConcrete (AyStreamDb abstractDb assumptions)
      (fun concreteH assumptionsH =>
        ay_stream_db_intro abstractDb assumptions
          (replay concreteH)
          assumptionsH)

theorem ay_stream_chunk_under_push
    (database : Prop) (active : Prop) (pushed : Prop)
    (beforeLog afterLog : Prop) :
    (AyStreamScope active pushed -> active) ->
    AyStreamChunk
      (AyStreamState database active beforeLog)
      (AyStreamState database active afterLog) ->
    AyStreamChunk
      (AyStreamState database (AyStreamScope active pushed) beforeLog)
      (AyStreamState database (AyStreamScope active pushed) afterLog) :=
  fun popProjection chunk scopedState =>
    scopedState
      (AyStreamState database (AyStreamScope active pushed) afterLog)
      (fun dbScope beforeLogH =>
        dbScope
          (AyStreamState database (AyStreamScope active pushed) afterLog)
          (fun databaseH scopedAssumptions =>
            ay_stream_state_intro database
              (AyStreamScope active pushed)
              afterLog
              (ay_stream_db_intro database
                (AyStreamScope active pushed)
                databaseH
                scopedAssumptions)
              (ay_stream_state_log database active afterLog
                (chunk
                  (ay_stream_state_intro database active beforeLog
                    (ay_stream_db_intro database active
                      databaseH
                      (popProjection scopedAssumptions))
                    beforeLogH))))))

theorem ay_stream_chunk_after_pop
    (database : Prop) (active : Prop) (pushed : Prop)
    (logState : Prop) :
    (AyStreamScope active pushed -> active) ->
    AyStreamState database (AyStreamScope active pushed) logState ->
    AyStreamState database active logState :=
  fun popProjection scopedState =>
    scopedState (AyStreamState database active logState)
      (fun dbScope logH =>
        dbScope (AyStreamState database active logState)
          (fun databaseH scopedAssumptions =>
            ay_stream_state_intro database active
              logState
              (ay_stream_db_intro database active
                databaseH
                (popProjection scopedAssumptions))
              logH))

theorem ay_stream_final_clause_preserved
    (startState : Prop) (endState : Prop) (finalClause : Prop) :
    AyStreamChunk startState endState ->
    AyStreamFinalClause endState finalClause ->
    startState ->
    finalClause :=
  fun chunk finalCheck startH =>
    finalCheck (chunk startH)

theorem ay_stream_final_clause_after_handoff
    (first : Prop) (middle : Prop) (last : Prop) (finalClause : Prop) :
    AyStreamChunk first middle ->
    AyStreamChunk middle last ->
    AyStreamFinalClause last finalClause ->
    first ->
    finalClause :=
  fun firstChunk secondChunk finalCheck firstH =>
    ay_stream_final_clause_preserved first last finalClause
      (ay_stream_chunk_handoff first middle last firstChunk secondChunk)
      finalCheck
      firstH

theorem ay_stream_final_clause_under_push_pop
    (database : Prop) (active : Prop) (pushed : Prop)
    (beforeLog afterLog : Prop) (finalClause : Prop) :
    AyStreamChunk
      (AyStreamState database active beforeLog)
      (AyStreamState database active afterLog) ->
    (AyStreamScope active pushed -> active) ->
    AyStreamFinalClause
      (AyStreamState database active afterLog)
      finalClause ->
    AyStreamState database (AyStreamScope active pushed) beforeLog ->
    finalClause :=
  fun chunk popProjection finalCheck scopedState =>
    finalCheck
      (ay_stream_chunk_after_pop database active pushed afterLog
        popProjection
        (ay_stream_chunk_under_push
          database active pushed beforeLog afterLog
          popProjection chunk scopedState))

theorem ay_stream_core_projection
    (formula : Prop) (activeAssumptions : Prop) (coreAssumptions : Prop) :
    AyStreamCoreCertificate formula activeAssumptions coreAssumptions ->
    activeAssumptions -> coreAssumptions :=
  fun certificate =>
    ay_stream_conj_left
      (activeAssumptions -> coreAssumptions)
      (formula -> coreAssumptions -> False)
      certificate

theorem ay_stream_core_conflict
    (formula : Prop) (activeAssumptions : Prop) (coreAssumptions : Prop) :
    AyStreamCoreCertificate formula activeAssumptions coreAssumptions ->
    formula -> coreAssumptions -> False :=
  fun certificate =>
    ay_stream_conj_right
      (activeAssumptions -> coreAssumptions)
      (formula -> coreAssumptions -> False)
      certificate

theorem ay_stream_core_through_replay
    (concreteFormula : Prop) (abstractFormula : Prop)
    (activeAssumptions : Prop) (coreAssumptions : Prop) :
    AyStreamReplay concreteFormula abstractFormula ->
    AyStreamCoreCertificate
      abstractFormula activeAssumptions coreAssumptions ->
    AyStreamDb concreteFormula activeAssumptions ->
    coreAssumptions :=
  fun _replay certificate scopedConcrete =>
    ay_stream_core_projection
      abstractFormula activeAssumptions coreAssumptions certificate
      (ay_stream_conj_right
        concreteFormula activeAssumptions scopedConcrete)

theorem ay_stream_conflict_through_replay
    (concreteFormula : Prop) (abstractFormula : Prop)
    (activeAssumptions : Prop) (coreAssumptions : Prop) :
    AyStreamReplay concreteFormula abstractFormula ->
    AyStreamCoreCertificate
      abstractFormula activeAssumptions coreAssumptions ->
    AyStreamDb concreteFormula activeAssumptions ->
    False :=
  fun replay certificate scopedConcrete =>
    ay_stream_core_conflict
      abstractFormula activeAssumptions coreAssumptions certificate
      (replay
        (ay_stream_conj_left
          concreteFormula activeAssumptions scopedConcrete))
      (ay_stream_core_through_replay
        concreteFormula abstractFormula activeAssumptions coreAssumptions
        replay certificate scopedConcrete)

theorem ay_stream_conflict_transport_preprocess
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (assumptions : Prop) :
    AyStreamPreprocessMap originalFormula preprocessedFormula ->
    (preprocessedFormula -> assumptions -> False) ->
    originalFormula -> assumptions -> False :=
  fun preprocess preConflict originalH assumptionsH =>
    preConflict
      (ay_stream_equisat_forward
        originalFormula preprocessedFormula preprocess originalH)
      assumptionsH

theorem ay_stream_core_transport_preprocess
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (activeAssumptions : Prop) (coreAssumptions : Prop) :
    AyStreamPreprocessMap originalFormula preprocessedFormula ->
    AyStreamCoreCertificate
      preprocessedFormula activeAssumptions coreAssumptions ->
    AyStreamCoreCertificate
      originalFormula activeAssumptions coreAssumptions :=
  fun preprocess certificate =>
    ay_stream_conj_intro
      (activeAssumptions -> coreAssumptions)
      (originalFormula -> coreAssumptions -> False)
      (ay_stream_core_projection
        preprocessedFormula activeAssumptions coreAssumptions certificate)
      (ay_stream_conflict_transport_preprocess
        originalFormula preprocessedFormula coreAssumptions preprocess
        (ay_stream_core_conflict
          preprocessedFormula activeAssumptions coreAssumptions
          certificate))

theorem ay_stream_replay_conflict_transport_preprocess
    (originalFormula : Prop) (preprocessedFormula : Prop)
    (abstractFormula : Prop)
    (activeAssumptions : Prop) (coreAssumptions : Prop) :
    AyStreamPreprocessMap originalFormula preprocessedFormula ->
    AyStreamReplay preprocessedFormula abstractFormula ->
    AyStreamCoreCertificate
      abstractFormula activeAssumptions coreAssumptions ->
    AyStreamDb originalFormula activeAssumptions ->
    False :=
  fun preprocess replay certificate originalScoped =>
    ay_stream_conflict_through_replay
      preprocessedFormula abstractFormula activeAssumptions coreAssumptions
      replay
      certificate
      (ay_stream_db_intro preprocessedFormula activeAssumptions
        (ay_stream_equisat_forward
          originalFormula preprocessedFormula preprocess
          (ay_stream_conj_left
            originalFormula activeAssumptions originalScoped))
        (ay_stream_conj_right
          originalFormula activeAssumptions originalScoped))
