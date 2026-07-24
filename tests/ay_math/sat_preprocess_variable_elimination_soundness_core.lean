-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded variable-elimination preprocessing soundness. The propositions stand
-- for original clauses, generated resolvents, eliminated-variable witnesses,
-- reconstruction/preprocessing maps, replay evidence, cache guards, accepted
-- reports, diagnostics, and public SAT/UNSAT outcomes.

def AyConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AySat (cnf : Prop) (model : Prop) :=
  AyConj cnf model

def AyReplay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def AyIdMatch (leftId : Prop) (rightId : Prop) :=
  AyConj (leftId -> rightId) (rightId -> leftId)

def AyDigestMatch (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj (cachedDigest -> runDigest) (runDigest -> cachedDigest)

def AyResolventGeneration
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop) :=
  AyConj
    eliminatedVariableWitness
    (originalClauses -> resolvents)

def AyReconstructionMap
    (eliminatedCnf : Prop) (originalCnf : Prop)
    (eliminatedModel : Prop) (originalModel : Prop) :=
  AyConj
    (AySat eliminatedCnf eliminatedModel -> AySat originalCnf originalModel)
    (originalCnf -> eliminatedCnf)

def AyPreprocessMap (originalCnf : Prop) (eliminatedCnf : Prop) :=
  AyEquisat originalCnf eliminatedCnf

def AyVariableEliminationGuards
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))

def AyAcceptedVariableEliminationReport
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyPreprocessMap originalCnf eliminatedCnf)
    (AyConj
      (AyResolventGeneration
        originalClauses resolvents eliminatedVariableWitness)
      (AyConj
        (AyReconstructionMap
          eliminatedCnf originalCnf eliminatedModel originalModel)
        (AyVariableEliminationGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))

def AyVariableEliminationFailure
    (invalidResolvent : Prop) (staleReplay : Prop)
    (digestMismatch : Prop) :=
  AyDisj invalidResolvent (AyDisj staleReplay digestMismatch)

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  AyConj currentCnf recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedVariableEliminationLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedVariableEliminationReport
      originalCnf eliminatedCnf originalClauses resolvents
      eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest)
    nextLog

def AyDiagnosticVariableEliminationLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (invalidResolvent : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyVariableEliminationFailure
        invalidResolvent staleReplay digestMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)))
    nextLog

def AyExitCodeSound (exitCode : Prop) (claim : Prop) :=
  AyConj exitCode claim

def AyPublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  AyDisj
    (AyExitCodeSound exitCode (AySat originalCnf model))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pbve_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_pbve_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pbve_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pbve_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_pbve_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_pbve_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pbve_conj_left (before -> after) (after -> before) eq

theorem ay_pbve_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pbve_conj_right (before -> after) (after -> before) eq

theorem ay_pbve_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_pbve_conj_left cnf model sat

theorem ay_pbve_sat_model
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    model := by
  intro sat
  exact ay_pbve_conj_right cnf model sat

theorem ay_pbve_report_map
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedVariableEliminationReport
      originalCnf eliminatedCnf originalClauses resolvents
      eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyPreprocessMap originalCnf eliminatedCnf := by
  intro accepted
  exact ay_pbve_conj_left
    (AyPreprocessMap originalCnf eliminatedCnf)
    (AyConj
      (AyResolventGeneration
        originalClauses resolvents eliminatedVariableWitness)
      (AyConj
        (AyReconstructionMap
          eliminatedCnf originalCnf eliminatedModel originalModel)
        (AyVariableEliminationGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))
    accepted

theorem ay_pbve_report_generation
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedVariableEliminationReport
      originalCnf eliminatedCnf originalClauses resolvents
      eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyResolventGeneration
      originalClauses resolvents eliminatedVariableWitness := by
  intro accepted
  exact ay_pbve_conj_left
    (AyResolventGeneration
      originalClauses resolvents eliminatedVariableWitness)
    (AyConj
      (AyReconstructionMap
        eliminatedCnf originalCnf eliminatedModel originalModel)
      (AyVariableEliminationGuards
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))
    (ay_pbve_conj_right
      (AyPreprocessMap originalCnf eliminatedCnf)
      (AyConj
        (AyResolventGeneration
          originalClauses resolvents eliminatedVariableWitness)
        (AyConj
          (AyReconstructionMap
            eliminatedCnf originalCnf eliminatedModel originalModel)
          (AyVariableEliminationGuards
            cachedEpoch currentEpoch cachedManifest runManifest
            cachedDigest runDigest)))
      accepted)

theorem ay_pbve_report_reconstruction
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedVariableEliminationReport
      originalCnf eliminatedCnf originalClauses resolvents
      eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyReconstructionMap eliminatedCnf originalCnf eliminatedModel originalModel := by
  intro accepted
  exact ay_pbve_conj_left
    (AyReconstructionMap eliminatedCnf originalCnf eliminatedModel originalModel)
    (AyVariableEliminationGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pbve_conj_right
      (AyResolventGeneration
        originalClauses resolvents eliminatedVariableWitness)
      (AyConj
        (AyReconstructionMap
          eliminatedCnf originalCnf eliminatedModel originalModel)
        (AyVariableEliminationGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      (ay_pbve_conj_right
        (AyPreprocessMap originalCnf eliminatedCnf)
        (AyConj
          (AyResolventGeneration
            originalClauses resolvents eliminatedVariableWitness)
          (AyConj
            (AyReconstructionMap
              eliminatedCnf originalCnf eliminatedModel originalModel)
            (AyVariableEliminationGuards
              cachedEpoch currentEpoch cachedManifest runManifest
              cachedDigest runDigest)))
        accepted))

theorem ay_pbve_report_guards
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedVariableEliminationReport
      originalCnf eliminatedCnf originalClauses resolvents
      eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyVariableEliminationGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest := by
  intro accepted
  exact ay_pbve_conj_right
    (AyReconstructionMap eliminatedCnf originalCnf eliminatedModel originalModel)
    (AyVariableEliminationGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pbve_conj_right
      (AyResolventGeneration
        originalClauses resolvents eliminatedVariableWitness)
      (AyConj
        (AyReconstructionMap
          eliminatedCnf originalCnf eliminatedModel originalModel)
        (AyVariableEliminationGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      (ay_pbve_conj_right
        (AyPreprocessMap originalCnf eliminatedCnf)
        (AyConj
          (AyResolventGeneration
            originalClauses resolvents eliminatedVariableWitness)
          (AyConj
            (AyReconstructionMap
              eliminatedCnf originalCnf eliminatedModel originalModel)
            (AyVariableEliminationGuards
              cachedEpoch currentEpoch cachedManifest runManifest
              cachedDigest runDigest)))
        accepted))

theorem ay_pbve_elimination_witness
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop) :
    AyResolventGeneration
      originalClauses resolvents eliminatedVariableWitness ->
    eliminatedVariableWitness := by
  intro generation
  exact ay_pbve_conj_left eliminatedVariableWitness
    (originalClauses -> resolvents)
    generation

theorem ay_pbve_resolvents_from_original
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop) :
    AyResolventGeneration
      originalClauses resolvents eliminatedVariableWitness ->
    originalClauses ->
    resolvents := by
  intro generation
  exact ay_pbve_conj_right eliminatedVariableWitness
    (originalClauses -> resolvents)
    generation

theorem ay_pbve_reconstruct_sat
    (eliminatedCnf : Prop) (originalCnf : Prop)
    (eliminatedModel : Prop) (originalModel : Prop) :
    AyReconstructionMap eliminatedCnf originalCnf eliminatedModel originalModel ->
    AySat eliminatedCnf eliminatedModel ->
    AySat originalCnf originalModel := by
  intro reconstruction
  exact ay_pbve_conj_left
    (AySat eliminatedCnf eliminatedModel -> AySat originalCnf originalModel)
    (originalCnf -> eliminatedCnf)
    reconstruction

theorem ay_pbve_original_to_eliminated
    (eliminatedCnf : Prop) (originalCnf : Prop)
    (eliminatedModel : Prop) (originalModel : Prop) :
    AyReconstructionMap eliminatedCnf originalCnf eliminatedModel originalModel ->
    originalCnf ->
    eliminatedCnf := by
  intro reconstruction
  exact ay_pbve_conj_right
    (AySat eliminatedCnf eliminatedModel -> AySat originalCnf originalModel)
    (originalCnf -> eliminatedCnf)
    reconstruction

theorem ay_pbve_accepted_semantics
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedVariableEliminationReport
      originalCnf eliminatedCnf originalClauses resolvents
      eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyEquisat originalCnf eliminatedCnf := by
  intro accepted
  exact ay_pbve_report_map originalCnf eliminatedCnf originalClauses
    resolvents eliminatedVariableWitness eliminatedModel originalModel
    cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
    runDigest accepted

theorem ay_pbve_sat_reconstruct_from_eliminated
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedVariableEliminationReport
      originalCnf eliminatedCnf originalClauses resolvents
      eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AySat eliminatedCnf eliminatedModel ->
    AySat originalCnf originalModel := by
  intro accepted
  exact ay_pbve_reconstruct_sat eliminatedCnf originalCnf
    eliminatedModel originalModel
    (ay_pbve_report_reconstruction originalCnf eliminatedCnf originalClauses
      resolvents eliminatedVariableWitness eliminatedModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest accepted)

theorem ay_pbve_sat_forward_to_eliminated
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedVariableEliminationReport
      originalCnf eliminatedCnf originalClauses resolvents
      eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    originalCnf ->
    eliminatedCnf := by
  intro accepted
  exact ay_pbve_equisat_forward originalCnf eliminatedCnf
    (ay_pbve_accepted_semantics originalCnf eliminatedCnf originalClauses
      resolvents eliminatedVariableWitness eliminatedModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest accepted)

theorem ay_pbve_unsat_pushback
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedVariableEliminationReport
      originalCnf eliminatedCnf originalClauses resolvents
      eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyReplay eliminatedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted
  intro replay
  intro hcertificate
  intro horiginal
  exact replay
    (ay_pbve_sat_forward_to_eliminated originalCnf eliminatedCnf
      originalClauses resolvents eliminatedVariableWitness eliminatedModel
      originalModel cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest accepted horiginal)
    hcertificate

theorem ay_pbve_accepted_log_report
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedVariableEliminationLogEntry
      previousLog nextLog originalCnf eliminatedCnf originalClauses
      resolvents eliminatedVariableWitness eliminatedModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyAcceptedVariableEliminationReport
      originalCnf eliminatedCnf originalClauses resolvents
      eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest := by
  intro entry
  exact ay_pbve_conj_left
    (AyAcceptedVariableEliminationReport
      originalCnf eliminatedCnf originalClauses resolvents
      eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest)
    nextLog
    (ay_pbve_conj_right previousLog
      (AyConj
        (AyAcceptedVariableEliminationReport
          originalCnf eliminatedCnf originalClauses resolvents
          eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
          currentEpoch cachedManifest runManifest cachedDigest runDigest)
        nextLog)
      entry)

theorem ay_pbve_accepted_log_append_only
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedVariableEliminationLogEntry
      previousLog nextLog originalCnf eliminatedCnf originalClauses
      resolvents eliminatedVariableWitness eliminatedModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyConj previousLog nextLog := by
  intro entry
  exact ay_pbve_conj_intro previousLog nextLog
    (ay_pbve_conj_left previousLog
      (AyConj
        (AyAcceptedVariableEliminationReport
          originalCnf eliminatedCnf originalClauses resolvents
          eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
          currentEpoch cachedManifest runManifest cachedDigest runDigest)
        nextLog)
      entry)
    (ay_pbve_conj_right
      (AyAcceptedVariableEliminationReport
        originalCnf eliminatedCnf originalClauses resolvents
        eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
        currentEpoch cachedManifest runManifest cachedDigest runDigest)
      nextLog
      (ay_pbve_conj_right previousLog
        (AyConj
          (AyAcceptedVariableEliminationReport
            originalCnf eliminatedCnf originalClauses resolvents
            eliminatedVariableWitness eliminatedModel originalModel cachedEpoch
            currentEpoch cachedManifest runManifest cachedDigest runDigest)
          nextLog)
        entry))

theorem ay_pbve_public_sat_from_eliminated
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedVariableEliminationLogEntry
      previousLog nextLog originalCnf eliminatedCnf originalClauses
      resolvents eliminatedVariableWitness eliminatedModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AySat eliminatedCnf eliminatedModel ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry
  intro sat
  intro hexit
  exact ay_pbve_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pbve_conj_intro exitCode (AySat originalCnf originalModel)
      hexit
      (ay_pbve_sat_reconstruct_from_eliminated originalCnf eliminatedCnf
        originalClauses resolvents eliminatedVariableWitness eliminatedModel
        originalModel cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest
        (ay_pbve_accepted_log_report previousLog nextLog originalCnf
          eliminatedCnf originalClauses resolvents eliminatedVariableWitness
          eliminatedModel originalModel cachedEpoch currentEpoch
          cachedManifest runManifest cachedDigest runDigest entry)
        sat))

theorem ay_pbve_public_unsat_from_eliminated
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (eliminatedCnf : Prop)
    (originalClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (eliminatedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedVariableEliminationLogEntry
      previousLog nextLog originalCnf eliminatedCnf originalClauses
      resolvents eliminatedVariableWitness eliminatedModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyReplay eliminatedCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry
  intro replay
  intro hexit
  exact ay_pbve_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pbve_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      (ay_pbve_unsat_pushback originalCnf eliminatedCnf originalClauses
        resolvents eliminatedVariableWitness eliminatedModel originalModel
        cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
        runDigest certificate conflict
        (ay_pbve_accepted_log_report previousLog nextLog originalCnf
          eliminatedCnf originalClauses resolvents eliminatedVariableWitness
          eliminatedModel originalModel cachedEpoch currentEpoch
          cachedManifest runManifest cachedDigest runDigest entry)
        replay))

theorem ay_pbve_failure_invalid_resolvent
    (invalidResolvent : Prop) (staleReplay : Prop)
    (digestMismatch : Prop) :
    invalidResolvent ->
    AyVariableEliminationFailure
      invalidResolvent staleReplay digestMismatch := by
  intro hinvalid
  exact ay_pbve_disj_left invalidResolvent
    (AyDisj staleReplay digestMismatch)
    hinvalid

theorem ay_pbve_failure_stale_replay
    (invalidResolvent : Prop) (staleReplay : Prop)
    (digestMismatch : Prop) :
    staleReplay ->
    AyVariableEliminationFailure
      invalidResolvent staleReplay digestMismatch := by
  intro hstale
  exact ay_pbve_disj_right invalidResolvent
    (AyDisj staleReplay digestMismatch)
    (ay_pbve_disj_left staleReplay digestMismatch hstale)

theorem ay_pbve_failure_digest_mismatch
    (invalidResolvent : Prop) (staleReplay : Prop)
    (digestMismatch : Prop) :
    digestMismatch ->
    AyVariableEliminationFailure
      invalidResolvent staleReplay digestMismatch := by
  intro hdigest
  exact ay_pbve_disj_right invalidResolvent
    (AyDisj staleReplay digestMismatch)
    (ay_pbve_disj_right staleReplay digestMismatch hdigest)

theorem ay_pbve_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (invalidResolvent : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticVariableEliminationLogEntry
      previousLog nextLog currentCnf invalidResolvent staleReplay
      digestMismatch recompute diagnostic ->
    AyVariableEliminationFailure
      invalidResolvent staleReplay digestMismatch := by
  intro entry
  exact ay_pbve_conj_left
    (AyVariableEliminationFailure
      invalidResolvent staleReplay digestMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pbve_conj_left
      (AyConj
        (AyVariableEliminationFailure
          invalidResolvent staleReplay digestMismatch)
        (AyConj
          (AyRecomputeObligation currentCnf recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_pbve_conj_right previousLog
        (AyConj
          (AyConj
            (AyVariableEliminationFailure
              invalidResolvent staleReplay digestMismatch)
            (AyConj
              (AyRecomputeObligation currentCnf recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_pbve_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (invalidResolvent : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticVariableEliminationLogEntry
      previousLog nextLog currentCnf invalidResolvent staleReplay
      digestMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_pbve_conj_right
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pbve_conj_right
      (AyVariableEliminationFailure
        invalidResolvent staleReplay digestMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pbve_conj_left
        (AyConj
          (AyVariableEliminationFailure
            invalidResolvent staleReplay digestMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pbve_conj_right previousLog
          (AyConj
            (AyConj
              (AyVariableEliminationFailure
                invalidResolvent staleReplay digestMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pbve_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (invalidResolvent : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticVariableEliminationLogEntry
      previousLog nextLog currentCnf invalidResolvent staleReplay
      digestMismatch recompute diagnostic ->
    AyRecomputeObligation currentCnf recompute := by
  intro entry
  exact ay_pbve_conj_left
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pbve_conj_right
      (AyVariableEliminationFailure
        invalidResolvent staleReplay digestMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pbve_conj_left
        (AyConj
          (AyVariableEliminationFailure
            invalidResolvent staleReplay digestMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pbve_conj_right previousLog
          (AyConj
            (AyConj
              (AyVariableEliminationFailure
                invalidResolvent staleReplay digestMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_preprocess_variable_elimination_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (invalidResolvent : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticVariableEliminationLogEntry
      previousLog nextLog currentCnf invalidResolvent staleReplay
      digestMismatch recompute diagnostic ->
    AyConj
      (AyVariableEliminationFailure
        invalidResolvent staleReplay digestMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_pbve_conj_intro
    (AyVariableEliminationFailure
      invalidResolvent staleReplay digestMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pbve_diagnostic_failure previousLog nextLog currentCnf
      invalidResolvent staleReplay digestMismatch recompute diagnostic entry)
    (ay_pbve_conj_intro
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pbve_diagnostic_recompute previousLog nextLog currentCnf
        invalidResolvent staleReplay digestMismatch recompute diagnostic entry)
      (ay_pbve_diagnostic_no_claim previousLog nextLog currentCnf
        invalidResolvent staleReplay digestMismatch recompute diagnostic entry))
