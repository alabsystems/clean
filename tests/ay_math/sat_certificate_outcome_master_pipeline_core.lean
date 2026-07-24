-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Master certificate outcome pipeline: preprocessing, solver outcome,
-- proof replay, visible model reconstruction, and final SAT/UNSAT packaging.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AyPreprocessingCertificate (original : Prop) (visible : Prop) :=
  AyEquisat original visible

def AySolverOutcome (visibleModel : Prop) (finalClause : Prop) :=
  AyDisj visibleModel finalClause

def AyProofReplay (visibleFormula : Prop) (finalClause : Prop) :=
  finalClause -> visibleFormula -> False

def AyVisibleModelReconstruction (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyFinalOutcome (originalModel : Prop) (originalUnsat : Prop) :=
  AyDisj originalModel originalUnsat

def AySatPackage (visibleModel : Prop) (originalModel : Prop) :=
  AyConj visibleModel (AyVisibleModelReconstruction visibleModel originalModel)

def AyUnsatPackage (finalClause : Prop) (originalUnsat : Prop) :=
  AyConj finalClause (finalClause -> originalUnsat)

def AyCertificateOutcomePipeline
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :=
  AyConj
    (AyPreprocessingCertificate originalFormula visibleFormula)
    (AyConj
      (AySolverOutcome visibleModel finalClause)
      (AyConj
        (AyProofReplay visibleFormula finalClause)
        (AyVisibleModelReconstruction visibleModel originalModel)))

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_conj_left
    (p : Prop) (q : Prop) :
    AyConj p q -> p := by
  intro both
  exact both p
    (fun hp _hq => hp)

theorem ay_disj_left
    (p : Prop) (q : Prop) :
    p -> AyDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_disj_right
    (p : Prop) (q : Prop) :
    q -> AyDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyEquisat before after := by
  intro forward
  intro backward
  exact ay_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before -> after := by
  intro equisat
  exact ay_conj_left
    (before -> after)
    (after -> before)
    equisat

theorem ay_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after -> before := by
  intro equisat
  exact equisat (after -> before)
    (fun _forward backward => backward)

theorem ay_preprocessing_to_visible
    (originalFormula : Prop) (visibleFormula : Prop) :
    AyPreprocessingCertificate originalFormula visibleFormula ->
    originalFormula -> visibleFormula := by
  intro preprocess
  exact ay_equisat_forward originalFormula visibleFormula preprocess

theorem ay_preprocessing_reconstruct_original
    (originalFormula : Prop) (visibleFormula : Prop) :
    AyPreprocessingCertificate originalFormula visibleFormula ->
    visibleFormula -> originalFormula := by
  intro preprocess
  exact ay_equisat_backward originalFormula visibleFormula preprocess

theorem ay_sat_package_intro
    (visibleModel : Prop) (originalModel : Prop) :
    AyVisibleModelReconstruction visibleModel originalModel ->
    visibleModel ->
    AySatPackage visibleModel originalModel := by
  intro reconstruct
  intro hvisible
  exact ay_conj_intro
    visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)
    hvisible
    reconstruct

theorem ay_sat_package_original_model
    (visibleModel : Prop) (originalModel : Prop) :
    AySatPackage visibleModel originalModel ->
    originalModel := by
  intro sat_package
  exact sat_package originalModel
    (fun hvisible reconstruct => reconstruct hvisible)

theorem ay_proof_replay_final_clause_sound
    (visibleFormula : Prop) (finalClause : Prop) :
    AyProofReplay visibleFormula finalClause ->
    finalClause ->
    visibleFormula -> False := by
  intro replay
  intro hfinal
  intro hvisible
  exact replay hfinal hvisible

theorem ay_unsat_from_replay_and_preprocessing
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyPreprocessingCertificate originalFormula visibleFormula ->
    AyProofReplay visibleFormula finalClause ->
    finalClause ->
    Not originalFormula := by
  intro preprocess
  intro replay
  intro hfinal
  intro horiginal
  exact replay hfinal
    (ay_preprocessing_to_visible
      originalFormula visibleFormula preprocess horiginal)

theorem ay_unsat_package_intro
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyPreprocessingCertificate originalFormula visibleFormula ->
    AyProofReplay visibleFormula finalClause ->
    finalClause ->
    AyUnsatPackage finalClause (Not originalFormula) := by
  intro preprocess
  intro replay
  intro hfinal
  exact ay_conj_intro finalClause (finalClause -> Not originalFormula)
    hfinal
    (fun hfinal_again =>
      ay_unsat_from_replay_and_preprocessing
        originalFormula visibleFormula finalClause
        preprocess replay hfinal_again)

theorem ay_unsat_package_original_unsat
    (finalClause : Prop) (originalUnsat : Prop) :
    AyUnsatPackage finalClause originalUnsat ->
    originalUnsat := by
  intro unsat_package
  exact unsat_package originalUnsat
    (fun hfinal final_to_unsat => final_to_unsat hfinal)

theorem ay_pipeline_project_preprocessing
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateOutcomePipeline
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyPreprocessingCertificate originalFormula visibleFormula := by
  intro pipeline
  exact pipeline
    (AyPreprocessingCertificate originalFormula visibleFormula)
    (fun preprocess _tail => preprocess)

theorem ay_pipeline_project_solver_outcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateOutcomePipeline
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AySolverOutcome visibleModel finalClause := by
  intro pipeline
  exact pipeline (AySolverOutcome visibleModel finalClause)
    (fun _preprocess tail =>
      tail (AySolverOutcome visibleModel finalClause)
        (fun outcome _tail2 => outcome))

theorem ay_pipeline_project_replay
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateOutcomePipeline
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyProofReplay visibleFormula finalClause := by
  intro pipeline
  exact pipeline (AyProofReplay visibleFormula finalClause)
    (fun _preprocess tail =>
      tail (AyProofReplay visibleFormula finalClause)
        (fun _outcome tail2 =>
          tail2 (AyProofReplay visibleFormula finalClause)
            (fun replay _reconstruct => replay)))

theorem ay_pipeline_project_reconstruction
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateOutcomePipeline
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyVisibleModelReconstruction visibleModel originalModel := by
  intro pipeline
  exact pipeline
    (AyVisibleModelReconstruction visibleModel originalModel)
    (fun _preprocess tail =>
      tail (AyVisibleModelReconstruction visibleModel originalModel)
        (fun _outcome tail2 =>
          tail2 (AyVisibleModelReconstruction visibleModel originalModel)
            (fun _replay reconstruct => reconstruct)))

theorem ay_pipeline_sat_branch_package
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateOutcomePipeline
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    visibleModel ->
    AySatPackage visibleModel originalModel := by
  intro pipeline
  intro hvisible_model
  exact ay_sat_package_intro visibleModel originalModel
    (ay_pipeline_project_reconstruction
      originalFormula visibleFormula visibleModel originalModel finalClause
      pipeline)
    hvisible_model

theorem ay_pipeline_unsat_branch_package
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateOutcomePipeline
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    finalClause ->
    AyUnsatPackage finalClause (Not originalFormula) := by
  intro pipeline
  intro hfinal
  exact ay_unsat_package_intro
    originalFormula visibleFormula finalClause
    (ay_pipeline_project_preprocessing
      originalFormula visibleFormula visibleModel originalModel finalClause
      pipeline)
    (ay_pipeline_project_replay
      originalFormula visibleFormula visibleModel originalModel finalClause
      pipeline)
    hfinal

theorem ay_pipeline_solver_outcome_final
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateOutcomePipeline
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyFinalOutcome originalModel (Not originalFormula) := by
  intro pipeline
  exact
    (ay_pipeline_project_solver_outcome
      originalFormula visibleFormula visibleModel originalModel finalClause
      pipeline)
      (AyFinalOutcome originalModel (Not originalFormula))
      (fun hvisible_model =>
        ay_disj_left originalModel (Not originalFormula)
          (ay_sat_package_original_model visibleModel originalModel
            (ay_pipeline_sat_branch_package
              originalFormula visibleFormula visibleModel originalModel
              finalClause pipeline hvisible_model)))
      (fun hfinal =>
        ay_disj_right originalModel (Not originalFormula)
          (ay_unsat_package_original_unsat finalClause (Not originalFormula)
            (ay_pipeline_unsat_branch_package
              originalFormula visibleFormula visibleModel originalModel
              finalClause pipeline hfinal)))

theorem ay_pipeline_sat_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateOutcomePipeline
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    visibleModel ->
    originalModel := by
  intro pipeline
  intro hvisible_model
  exact ay_sat_package_original_model visibleModel originalModel
    (ay_pipeline_sat_branch_package
      originalFormula visibleFormula visibleModel originalModel finalClause
      pipeline hvisible_model)

theorem ay_pipeline_unsat_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop)
    (finalClause : Prop) :
    AyCertificateOutcomePipeline
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    finalClause ->
    Not originalFormula := by
  intro pipeline
  intro hfinal
  exact ay_unsat_package_original_unsat finalClause (Not originalFormula)
    (ay_pipeline_unsat_branch_package
      originalFormula visibleFormula visibleModel originalModel finalClause
      pipeline hfinal)
