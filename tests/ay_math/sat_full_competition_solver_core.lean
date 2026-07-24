-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked abstraction for full SAT-COMP sequential solver soundness:
-- certified preprocessing, watched propagation, CDCL, restarts, streaming
-- proof replay, and final SAT/UNSAT outcome transport. Propositions stand for
-- solver states, certificates, models, and final clauses; the maps between
-- them are explicit Church-encoded certificates.

def AyFCSConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyFCSDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyFCSEquisat (before : Prop) (after : Prop) :=
  AyFCSConj (before -> after) (after -> before)

def AyFCSMap (source : Prop) (target : Prop) :=
  source -> target

def AyFCSTransport (visible : Prop) (original : Prop) :=
  visible -> original

def AyFCSPreprocessCert
    (original : Prop) (preprocessed : Prop)
    (visibleModel : Prop) (originalModel : Prop) :=
  AyFCSConj
    (AyFCSEquisat original preprocessed)
    (AyFCSTransport visibleModel originalModel)

def AyFCSWatchCert (preprocessed : Prop) (watchedState : Prop) :=
  AyFCSMap preprocessed watchedState

def AyFCSCDCLCert (watchedState : Prop) (cdclState : Prop) :=
  AyFCSMap watchedState cdclState

def AyFCSRestartCert (cdclState : Prop) (restartState : Prop) :=
  AyFCSEquisat cdclState restartState

def AyFCSStreamingCert (restartState : Prop) (replayState : Prop) :=
  AyFCSMap restartState replayState

def AyFCSSatOutcome (solverModel : Prop) (visibleModel : Prop) :=
  AyFCSConj solverModel (solverModel -> visibleModel)

def AyFCSUnsatOutcome (finalClause : Prop) (preprocessedUnsat : Prop) :=
  AyFCSConj finalClause (finalClause -> preprocessedUnsat)

def AyFCSFinalOutcome (satWitness : Prop) (unsatWitness : Prop) :=
  AyFCSDisj satWitness unsatWitness

def AyFCSSolverPipeline
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop) :=
  AyFCSConj
    (AyFCSPreprocessCert original preprocessed visibleModel originalModel)
    (AyFCSConj
      (AyFCSWatchCert preprocessed watchedState)
      (AyFCSConj
        (AyFCSCDCLCert watchedState cdclState)
        (AyFCSConj
          (AyFCSRestartCert cdclState restartState)
          (AyFCSStreamingCert restartState replayState))))

theorem ay_fcs_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyFCSConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_fcs_conj_left
    (p : Prop) (q : Prop) :
    AyFCSConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_fcs_disj_left
    (p : Prop) (q : Prop) :
    p -> AyFCSDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_fcs_disj_right
    (p : Prop) (q : Prop) :
    q -> AyFCSDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_fcs_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyFCSEquisat before after := by
  intro forward
  intro backward
  exact ay_fcs_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_fcs_equisat_forward
    (before : Prop) (after : Prop) :
    AyFCSEquisat before after ->
    before ->
    after := by
  intro certificate
  exact certificate (before -> after)
    (fun forward _backward => forward)

theorem ay_fcs_equisat_backward
    (before : Prop) (after : Prop) :
    AyFCSEquisat before after ->
    after ->
    before := by
  intro certificate
  exact certificate (after -> before)
    (fun _forward backward => backward)

theorem ay_fcs_equisat_compose
    (before : Prop) (middle : Prop) (after : Prop) :
    AyFCSEquisat before middle ->
    AyFCSEquisat middle after ->
    AyFCSEquisat before after :=
  fun first second result build =>
    first result
      (fun first_forward first_backward =>
        second result
          (fun second_forward second_backward =>
            build
              (fun hbefore => second_forward (first_forward hbefore))
              (fun hafter => first_backward (second_backward hafter))))

theorem ay_fcs_preprocess_equisat
    (original : Prop) (preprocessed : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyFCSPreprocessCert original preprocessed visibleModel originalModel ->
    AyFCSEquisat original preprocessed := by
  intro cert
  exact ay_fcs_conj_left
    (AyFCSEquisat original preprocessed)
    (AyFCSTransport visibleModel originalModel)
    cert

theorem ay_fcs_preprocess_model_transport
    (original : Prop) (preprocessed : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyFCSPreprocessCert original preprocessed visibleModel originalModel ->
    visibleModel ->
    originalModel := by
  intro cert
  exact cert (visibleModel -> originalModel)
    (fun _equisat transport => transport)

theorem ay_fcs_pipeline_preprocess
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    AyFCSPreprocessCert original preprocessed visibleModel originalModel := by
  intro pipeline
  exact ay_fcs_conj_left
    (AyFCSPreprocessCert original preprocessed visibleModel originalModel)
    (AyFCSConj
      (AyFCSWatchCert preprocessed watchedState)
      (AyFCSConj
        (AyFCSCDCLCert watchedState cdclState)
        (AyFCSConj
          (AyFCSRestartCert cdclState restartState)
          (AyFCSStreamingCert restartState replayState))))
    pipeline

theorem ay_fcs_pipeline_watch
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    AyFCSWatchCert preprocessed watchedState := by
  intro pipeline
  exact pipeline (AyFCSWatchCert preprocessed watchedState)
    (fun _preprocess rest =>
      rest (AyFCSWatchCert preprocessed watchedState)
        (fun watch _tail => watch))

theorem ay_fcs_pipeline_cdcl
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    AyFCSCDCLCert watchedState cdclState := by
  intro pipeline
  exact pipeline (AyFCSCDCLCert watchedState cdclState)
    (fun _preprocess rest =>
      rest (AyFCSCDCLCert watchedState cdclState)
        (fun _watch tail =>
          tail (AyFCSCDCLCert watchedState cdclState)
            (fun cdcl _tail => cdcl)))

theorem ay_fcs_pipeline_restart
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    AyFCSRestartCert cdclState restartState := by
  intro pipeline
  exact pipeline (AyFCSRestartCert cdclState restartState)
    (fun _preprocess rest =>
      rest (AyFCSRestartCert cdclState restartState)
        (fun _watch tail =>
          tail (AyFCSRestartCert cdclState restartState)
            (fun _cdcl final_tail =>
              final_tail (AyFCSRestartCert cdclState restartState)
                (fun restart _stream => restart))))

theorem ay_fcs_pipeline_streaming
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    AyFCSStreamingCert restartState replayState := by
  intro pipeline
  exact pipeline (AyFCSStreamingCert restartState replayState)
    (fun _preprocess rest =>
      rest (AyFCSStreamingCert restartState replayState)
        (fun _watch tail =>
          tail (AyFCSStreamingCert restartState replayState)
            (fun _cdcl final_tail =>
              final_tail (AyFCSStreamingCert restartState replayState)
                (fun _restart stream => stream))))

theorem ay_fcs_preprocess_to_replay
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    preprocessed ->
    replayState := by
  intro pipeline
  intro hpreprocessed
  exact ay_fcs_pipeline_streaming
    original preprocessed watchedState cdclState restartState replayState
    visibleModel originalModel pipeline
    (ay_fcs_equisat_forward cdclState restartState
      (ay_fcs_pipeline_restart
        original preprocessed watchedState cdclState restartState replayState
        visibleModel originalModel pipeline)
      ((ay_fcs_pipeline_cdcl
        original preprocessed watchedState cdclState restartState replayState
        visibleModel originalModel pipeline)
        ((ay_fcs_pipeline_watch
          original preprocessed watchedState cdclState restartState replayState
          visibleModel originalModel pipeline)
          hpreprocessed)))

theorem ay_fcs_original_to_replay
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    original ->
    replayState := by
  intro pipeline
  intro horiginal
  exact ay_fcs_preprocess_to_replay
    original preprocessed watchedState cdclState restartState replayState
    visibleModel originalModel pipeline
    (ay_fcs_equisat_forward original preprocessed
      (ay_fcs_preprocess_equisat original preprocessed visibleModel originalModel
        (ay_fcs_pipeline_preprocess
          original preprocessed watchedState cdclState restartState replayState
          visibleModel originalModel pipeline))
      horiginal)

theorem ay_fcs_replay_to_original
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    (replayState -> preprocessed) ->
    replayState ->
    original := by
  intro pipeline
  intro replay_to_preprocessed
  intro hreplay
  exact ay_fcs_equisat_backward original preprocessed
    (ay_fcs_preprocess_equisat original preprocessed visibleModel originalModel
      (ay_fcs_pipeline_preprocess
        original preprocessed watchedState cdclState restartState replayState
        visibleModel originalModel pipeline))
    (replay_to_preprocessed hreplay)

theorem ay_fcs_solver_equisat_original_replay
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    (replayState -> preprocessed) ->
    AyFCSEquisat original replayState := by
  intro pipeline
  intro replay_to_preprocessed
  exact ay_fcs_equisat_intro original replayState
    (ay_fcs_original_to_replay
      original preprocessed watchedState cdclState restartState replayState
      visibleModel originalModel pipeline)
    (ay_fcs_replay_to_original
      original preprocessed watchedState cdclState restartState replayState
      visibleModel originalModel pipeline replay_to_preprocessed)

theorem ay_fcs_sat_outcome_intro
    (solverModel : Prop) (visibleModel : Prop) :
    solverModel ->
    (solverModel -> visibleModel) ->
    AyFCSSatOutcome solverModel visibleModel := by
  intro hsolver
  intro project
  exact ay_fcs_conj_intro solverModel (solverModel -> visibleModel)
    hsolver
    project

theorem ay_fcs_sat_visible_model
    (solverModel : Prop) (visibleModel : Prop) :
    AyFCSSatOutcome solverModel visibleModel ->
    visibleModel := by
  intro outcome
  exact outcome visibleModel (fun hsolver project => project hsolver)

theorem ay_fcs_sat_original_model
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (solverModel : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    AyFCSSatOutcome solverModel visibleModel ->
    originalModel := by
  intro pipeline
  intro sat
  exact ay_fcs_preprocess_model_transport original preprocessed
    visibleModel originalModel
    (ay_fcs_pipeline_preprocess
      original preprocessed watchedState cdclState restartState replayState
      visibleModel originalModel pipeline)
    (ay_fcs_sat_visible_model solverModel visibleModel sat)

theorem ay_fcs_unsat_outcome_intro
    (finalClause : Prop) (preprocessedUnsat : Prop) :
    finalClause ->
    (finalClause -> preprocessedUnsat) ->
    AyFCSUnsatOutcome finalClause preprocessedUnsat := by
  intro hfinal
  intro close
  exact ay_fcs_conj_intro finalClause (finalClause -> preprocessedUnsat)
    hfinal
    close

theorem ay_fcs_unsat_preprocessed
    (finalClause : Prop) (preprocessedUnsat : Prop) :
    AyFCSUnsatOutcome finalClause preprocessedUnsat ->
    preprocessedUnsat := by
  intro outcome
  exact outcome preprocessedUnsat (fun hfinal close => close hfinal)

theorem ay_fcs_unsat_original
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) (preprocessedUnsat : Prop)
    (originalUnsat : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    AyFCSUnsatOutcome finalClause preprocessedUnsat ->
    (preprocessedUnsat -> originalUnsat) ->
    originalUnsat := by
  intro _pipeline
  intro unsat
  intro lift_unsat
  exact lift_unsat (ay_fcs_unsat_preprocessed finalClause preprocessedUnsat unsat)

theorem ay_fcs_final_outcome_sat
    (satWitness : Prop) (unsatWitness : Prop) :
    satWitness ->
    AyFCSFinalOutcome satWitness unsatWitness := by
  intro sat
  exact ay_fcs_disj_left satWitness unsatWitness sat

theorem ay_fcs_final_outcome_unsat
    (satWitness : Prop) (unsatWitness : Prop) :
    unsatWitness ->
    AyFCSFinalOutcome satWitness unsatWitness := by
  intro unsat
  exact ay_fcs_disj_right satWitness unsatWitness unsat

theorem ay_fcs_final_outcome_transport
    (satWitness : Prop) (unsatWitness : Prop)
    (originalSat : Prop) (originalUnsat : Prop) :
    AyFCSFinalOutcome satWitness unsatWitness ->
    (satWitness -> originalSat) ->
    (unsatWitness -> originalUnsat) ->
    AyFCSFinalOutcome originalSat originalUnsat := by
  intro outcome
  intro sat_transport
  intro unsat_transport
  exact outcome (AyFCSFinalOutcome originalSat originalUnsat)
    (fun sat => ay_fcs_final_outcome_sat originalSat originalUnsat
      (sat_transport sat))
    (fun unsat => ay_fcs_final_outcome_unsat originalSat originalUnsat
      (unsat_transport unsat))

theorem ay_fcs_full_solver_sat_branch_sound
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (solverModel : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    AyFCSSatOutcome solverModel visibleModel ->
    AyFCSFinalOutcome originalModel False := by
  intro pipeline
  intro sat
  exact ay_fcs_final_outcome_sat originalModel False
    (ay_fcs_sat_original_model
      original preprocessed watchedState cdclState restartState replayState
      visibleModel originalModel solverModel pipeline sat)

theorem ay_fcs_full_solver_unsat_branch_sound
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) (preprocessedUnsat : Prop)
    (originalUnsat : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    AyFCSUnsatOutcome finalClause preprocessedUnsat ->
    (preprocessedUnsat -> originalUnsat) ->
    AyFCSFinalOutcome False originalUnsat := by
  intro pipeline
  intro unsat
  intro lift_unsat
  exact ay_fcs_final_outcome_unsat False originalUnsat
    (ay_fcs_unsat_original
      original preprocessed watchedState cdclState restartState replayState
      visibleModel originalModel finalClause preprocessedUnsat originalUnsat
      pipeline unsat lift_unsat)

theorem ay_fcs_full_competition_solver_sound
    (original : Prop) (preprocessed : Prop)
    (watchedState : Prop) (cdclState : Prop)
    (restartState : Prop) (replayState : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (solverModel : Prop) (finalClause : Prop)
    (preprocessedUnsat : Prop) (originalUnsat : Prop) :
    AyFCSSolverPipeline original preprocessed watchedState cdclState
      restartState replayState visibleModel originalModel ->
    AyFCSFinalOutcome
      (AyFCSSatOutcome solverModel visibleModel)
      (AyFCSUnsatOutcome finalClause preprocessedUnsat) ->
    (preprocessedUnsat -> originalUnsat) ->
    AyFCSFinalOutcome originalModel originalUnsat := by
  intro pipeline
  intro outcome
  intro lift_unsat
  exact outcome (AyFCSFinalOutcome originalModel originalUnsat)
    (fun sat => ay_fcs_final_outcome_sat originalModel originalUnsat
      (ay_fcs_sat_original_model
        original preprocessed watchedState cdclState restartState replayState
        visibleModel originalModel solverModel pipeline sat))
    (fun unsat => ay_fcs_final_outcome_unsat originalModel originalUnsat
      (ay_fcs_unsat_original
        original preprocessed watchedState cdclState restartState replayState
        visibleModel originalModel finalClause preprocessedUnsat originalUnsat
        pipeline unsat lift_unsat))
