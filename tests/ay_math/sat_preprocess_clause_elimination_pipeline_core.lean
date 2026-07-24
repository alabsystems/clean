-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Integrated clause-elimination preprocessing pipeline soundness. The
-- propositions stand for subsumption, blocked-clause elimination, bounded
-- variable elimination, replay witnesses, reconstruction maps, guard evidence,
-- accepted reports, diagnostics, and public SAT/UNSAT outcomes.

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

def AySubsumptionStage
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) :=
  AyConj
    (originalClauses -> subsumedClauses)
    (strengthenedClauses -> subsumedClauses)

def AyBlockedClauseStage
    (subsumedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) :=
  AyConj blockerWitness (subsumedClauses -> blockedClauses)

def AyVariableEliminationStage
    (blockedClauses : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop) :=
  AyConj eliminatedVariableWitness (blockedClauses -> resolvents)

def AyClauseEliminationPipeline
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop) :=
  AyConj
    (AySubsumptionStage
      originalClauses subsumedClauses strengthenedClauses)
    (AyConj
      (AyBlockedClauseStage
        subsumedClauses blockedClauses blockerWitness)
      (AyVariableEliminationStage
        blockedClauses resolvents eliminatedVariableWitness))

def AyReconstructionMap
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :=
  AyConj
    (AySat finalCnf finalModel -> AySat originalCnf originalModel)
    (originalCnf -> finalCnf)

def AyPreprocessMap (originalCnf : Prop) (finalCnf : Prop) :=
  AyEquisat originalCnf finalCnf

def AyPipelineGuards
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))

def AyAcceptedPipelineReport
    (originalCnf : Prop) (finalCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyPreprocessMap originalCnf finalCnf)
    (AyConj
      (AyClauseEliminationPipeline
        originalClauses subsumedClauses strengthenedClauses
        blockedClauses blockerWitness resolvents
        eliminatedVariableWitness)
      (AyConj
        (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
        (AyPipelineGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))

def AyPipelineFailure
    (subsumptionFailure : Prop)
    (blockedClauseFailure : Prop)
    (variableEliminationFailure : Prop) :=
  AyDisj subsumptionFailure
    (AyDisj blockedClauseFailure variableEliminationFailure)

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  AyConj currentCnf recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedPipelineLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedPipelineReport
      originalCnf finalCnf originalClauses subsumedClauses
      strengthenedClauses blockedClauses blockerWitness resolvents
      eliminatedVariableWitness finalModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest)
    nextLog

def AyDiagnosticPipelineLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (subsumptionFailure : Prop)
    (blockedClauseFailure : Prop)
    (variableEliminationFailure : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyPipelineFailure
        subsumptionFailure blockedClauseFailure variableEliminationFailure)
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

theorem ay_pcep_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_pcep_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pcep_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pcep_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_pcep_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_pcep_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pcep_conj_left (before -> after) (after -> before) eq

theorem ay_pcep_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pcep_conj_right (before -> after) (after -> before) eq

theorem ay_pcep_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_pcep_conj_left cnf model sat

theorem ay_pcep_sat_model
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    model := by
  intro sat
  exact ay_pcep_conj_right cnf model sat

theorem ay_pcep_report_map
    (originalCnf : Prop) (finalCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedPipelineReport
      originalCnf finalCnf originalClauses subsumedClauses
      strengthenedClauses blockedClauses blockerWitness resolvents
      eliminatedVariableWitness finalModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyPreprocessMap originalCnf finalCnf := by
  intro accepted
  exact ay_pcep_conj_left
    (AyPreprocessMap originalCnf finalCnf)
    (AyConj
      (AyClauseEliminationPipeline
        originalClauses subsumedClauses strengthenedClauses
        blockedClauses blockerWitness resolvents
        eliminatedVariableWitness)
      (AyConj
        (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
        (AyPipelineGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))
    accepted

theorem ay_pcep_report_pipeline
    (originalCnf : Prop) (finalCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedPipelineReport
      originalCnf finalCnf originalClauses subsumedClauses
      strengthenedClauses blockedClauses blockerWitness resolvents
      eliminatedVariableWitness finalModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyClauseEliminationPipeline
      originalClauses subsumedClauses strengthenedClauses
      blockedClauses blockerWitness resolvents eliminatedVariableWitness := by
  intro accepted
  exact ay_pcep_conj_left
    (AyClauseEliminationPipeline
      originalClauses subsumedClauses strengthenedClauses
      blockedClauses blockerWitness resolvents eliminatedVariableWitness)
    (AyConj
      (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
      (AyPipelineGuards
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))
    (ay_pcep_conj_right
      (AyPreprocessMap originalCnf finalCnf)
      (AyConj
        (AyClauseEliminationPipeline
          originalClauses subsumedClauses strengthenedClauses
          blockedClauses blockerWitness resolvents
          eliminatedVariableWitness)
        (AyConj
          (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
          (AyPipelineGuards
            cachedEpoch currentEpoch cachedManifest runManifest
            cachedDigest runDigest)))
      accepted)

theorem ay_pcep_report_reconstruction
    (originalCnf : Prop) (finalCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedPipelineReport
      originalCnf finalCnf originalClauses subsumedClauses
      strengthenedClauses blockedClauses blockerWitness resolvents
      eliminatedVariableWitness finalModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyReconstructionMap finalCnf originalCnf finalModel originalModel := by
  intro accepted
  exact ay_pcep_conj_left
    (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
    (AyPipelineGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pcep_conj_right
      (AyClauseEliminationPipeline
        originalClauses subsumedClauses strengthenedClauses
        blockedClauses blockerWitness resolvents eliminatedVariableWitness)
      (AyConj
        (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
        (AyPipelineGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      (ay_pcep_conj_right
        (AyPreprocessMap originalCnf finalCnf)
        (AyConj
          (AyClauseEliminationPipeline
            originalClauses subsumedClauses strengthenedClauses
            blockedClauses blockerWitness resolvents
            eliminatedVariableWitness)
          (AyConj
            (AyReconstructionMap finalCnf originalCnf finalModel originalModel)
            (AyPipelineGuards
              cachedEpoch currentEpoch cachedManifest runManifest
              cachedDigest runDigest)))
        accepted))

theorem ay_pcep_subsumption_stage
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop) :
    AyClauseEliminationPipeline
      originalClauses subsumedClauses strengthenedClauses
      blockedClauses blockerWitness resolvents eliminatedVariableWitness ->
    AySubsumptionStage originalClauses subsumedClauses strengthenedClauses := by
  intro pipeline
  exact ay_pcep_conj_left
    (AySubsumptionStage originalClauses subsumedClauses strengthenedClauses)
    (AyConj
      (AyBlockedClauseStage subsumedClauses blockedClauses blockerWitness)
      (AyVariableEliminationStage
        blockedClauses resolvents eliminatedVariableWitness))
    pipeline

theorem ay_pcep_blocked_stage
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop) :
    AyClauseEliminationPipeline
      originalClauses subsumedClauses strengthenedClauses
      blockedClauses blockerWitness resolvents eliminatedVariableWitness ->
    AyBlockedClauseStage subsumedClauses blockedClauses blockerWitness := by
  intro pipeline
  exact ay_pcep_conj_left
    (AyBlockedClauseStage subsumedClauses blockedClauses blockerWitness)
    (AyVariableEliminationStage
      blockedClauses resolvents eliminatedVariableWitness)
    (ay_pcep_conj_right
      (AySubsumptionStage
        originalClauses subsumedClauses strengthenedClauses)
      (AyConj
        (AyBlockedClauseStage subsumedClauses blockedClauses blockerWitness)
        (AyVariableEliminationStage
          blockedClauses resolvents eliminatedVariableWitness))
      pipeline)

theorem ay_pcep_variable_stage
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop) :
    AyClauseEliminationPipeline
      originalClauses subsumedClauses strengthenedClauses
      blockedClauses blockerWitness resolvents eliminatedVariableWitness ->
    AyVariableEliminationStage
      blockedClauses resolvents eliminatedVariableWitness := by
  intro pipeline
  exact ay_pcep_conj_right
    (AyBlockedClauseStage subsumedClauses blockedClauses blockerWitness)
    (AyVariableEliminationStage
      blockedClauses resolvents eliminatedVariableWitness)
    (ay_pcep_conj_right
      (AySubsumptionStage
        originalClauses subsumedClauses strengthenedClauses)
      (AyConj
        (AyBlockedClauseStage subsumedClauses blockedClauses blockerWitness)
        (AyVariableEliminationStage
          blockedClauses resolvents eliminatedVariableWitness))
      pipeline)

theorem ay_pcep_reconstruct_sat
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :
    AyReconstructionMap finalCnf originalCnf finalModel originalModel ->
    AySat finalCnf finalModel ->
    AySat originalCnf originalModel := by
  intro reconstruction
  exact ay_pcep_conj_left
    (AySat finalCnf finalModel -> AySat originalCnf originalModel)
    (originalCnf -> finalCnf)
    reconstruction

theorem ay_pcep_original_to_final
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :
    AyReconstructionMap finalCnf originalCnf finalModel originalModel ->
    originalCnf ->
    finalCnf := by
  intro reconstruction
  exact ay_pcep_conj_right
    (AySat finalCnf finalModel -> AySat originalCnf originalModel)
    (originalCnf -> finalCnf)
    reconstruction

theorem ay_pcep_accepted_semantics
    (originalCnf : Prop) (finalCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedPipelineReport
      originalCnf finalCnf originalClauses subsumedClauses
      strengthenedClauses blockedClauses blockerWitness resolvents
      eliminatedVariableWitness finalModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyEquisat originalCnf finalCnf := by
  intro accepted
  exact ay_pcep_report_map originalCnf finalCnf originalClauses
    subsumedClauses strengthenedClauses blockedClauses blockerWitness
    resolvents eliminatedVariableWitness finalModel originalModel
    cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
    runDigest accepted

theorem ay_pcep_sat_reconstruct_from_final
    (originalCnf : Prop) (finalCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedPipelineReport
      originalCnf finalCnf originalClauses subsumedClauses
      strengthenedClauses blockedClauses blockerWitness resolvents
      eliminatedVariableWitness finalModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AySat finalCnf finalModel ->
    AySat originalCnf originalModel := by
  intro accepted
  exact ay_pcep_reconstruct_sat finalCnf originalCnf finalModel originalModel
    (ay_pcep_report_reconstruction originalCnf finalCnf originalClauses
      subsumedClauses strengthenedClauses blockedClauses blockerWitness
      resolvents eliminatedVariableWitness finalModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest accepted)

theorem ay_pcep_unsat_pushback
    (originalCnf : Prop) (finalCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedPipelineReport
      originalCnf finalCnf originalClauses subsumedClauses
      strengthenedClauses blockedClauses blockerWitness resolvents
      eliminatedVariableWitness finalModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyReplay finalCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted
  intro replay
  intro hcertificate
  intro horiginal
  exact replay
    (ay_pcep_equisat_forward originalCnf finalCnf
      (ay_pcep_accepted_semantics originalCnf finalCnf originalClauses
        subsumedClauses strengthenedClauses blockedClauses blockerWitness
        resolvents eliminatedVariableWitness finalModel originalModel
        cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
        runDigest accepted)
      horiginal)
    hcertificate

theorem ay_pcep_accepted_log_report
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedPipelineLogEntry
      previousLog nextLog originalCnf finalCnf originalClauses
      subsumedClauses strengthenedClauses blockedClauses blockerWitness
      resolvents eliminatedVariableWitness finalModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyAcceptedPipelineReport
      originalCnf finalCnf originalClauses subsumedClauses
      strengthenedClauses blockedClauses blockerWitness resolvents
      eliminatedVariableWitness finalModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest := by
  intro entry
  exact ay_pcep_conj_left
    (AyAcceptedPipelineReport
      originalCnf finalCnf originalClauses subsumedClauses
      strengthenedClauses blockedClauses blockerWitness resolvents
      eliminatedVariableWitness finalModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest)
    nextLog
    (ay_pcep_conj_right previousLog
      (AyConj
        (AyAcceptedPipelineReport
          originalCnf finalCnf originalClauses subsumedClauses
          strengthenedClauses blockedClauses blockerWitness resolvents
          eliminatedVariableWitness finalModel originalModel cachedEpoch
          currentEpoch cachedManifest runManifest cachedDigest runDigest)
        nextLog)
      entry)

theorem ay_pcep_public_sat_from_final
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedPipelineLogEntry
      previousLog nextLog originalCnf finalCnf originalClauses
      subsumedClauses strengthenedClauses blockedClauses blockerWitness
      resolvents eliminatedVariableWitness finalModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AySat finalCnf finalModel ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry
  intro sat
  intro hexit
  exact ay_pcep_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pcep_conj_intro exitCode (AySat originalCnf originalModel)
      hexit
      (ay_pcep_sat_reconstruct_from_final originalCnf finalCnf
        originalClauses subsumedClauses strengthenedClauses blockedClauses
        blockerWitness resolvents eliminatedVariableWitness finalModel
        originalModel cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest
        (ay_pcep_accepted_log_report previousLog nextLog originalCnf
          finalCnf originalClauses subsumedClauses strengthenedClauses
          blockedClauses blockerWitness resolvents eliminatedVariableWitness
          finalModel originalModel cachedEpoch currentEpoch cachedManifest
          runManifest cachedDigest runDigest entry)
        sat))

theorem ay_pcep_public_unsat_from_final
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (finalCnf : Prop)
    (originalClauses : Prop) (subsumedClauses : Prop)
    (strengthenedClauses : Prop) (blockedClauses : Prop)
    (blockerWitness : Prop) (resolvents : Prop)
    (eliminatedVariableWitness : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedPipelineLogEntry
      previousLog nextLog originalCnf finalCnf originalClauses
      subsumedClauses strengthenedClauses blockedClauses blockerWitness
      resolvents eliminatedVariableWitness finalModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyReplay finalCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry
  intro replay
  intro hexit
  exact ay_pcep_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pcep_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      (ay_pcep_unsat_pushback originalCnf finalCnf originalClauses
        subsumedClauses strengthenedClauses blockedClauses blockerWitness
        resolvents eliminatedVariableWitness finalModel originalModel
        cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
        runDigest certificate conflict
        (ay_pcep_accepted_log_report previousLog nextLog originalCnf
          finalCnf originalClauses subsumedClauses strengthenedClauses
          blockedClauses blockerWitness resolvents eliminatedVariableWitness
          finalModel originalModel cachedEpoch currentEpoch cachedManifest
          runManifest cachedDigest runDigest entry)
        replay))

theorem ay_pcep_failure_subsumption
    (subsumptionFailure : Prop)
    (blockedClauseFailure : Prop)
    (variableEliminationFailure : Prop) :
    subsumptionFailure ->
    AyPipelineFailure
      subsumptionFailure blockedClauseFailure variableEliminationFailure := by
  intro hfailure
  exact ay_pcep_disj_left subsumptionFailure
    (AyDisj blockedClauseFailure variableEliminationFailure)
    hfailure

theorem ay_pcep_failure_blocked_clause
    (subsumptionFailure : Prop)
    (blockedClauseFailure : Prop)
    (variableEliminationFailure : Prop) :
    blockedClauseFailure ->
    AyPipelineFailure
      subsumptionFailure blockedClauseFailure variableEliminationFailure := by
  intro hfailure
  exact ay_pcep_disj_right subsumptionFailure
    (AyDisj blockedClauseFailure variableEliminationFailure)
    (ay_pcep_disj_left blockedClauseFailure variableEliminationFailure
      hfailure)

theorem ay_pcep_failure_variable_elimination
    (subsumptionFailure : Prop)
    (blockedClauseFailure : Prop)
    (variableEliminationFailure : Prop) :
    variableEliminationFailure ->
    AyPipelineFailure
      subsumptionFailure blockedClauseFailure variableEliminationFailure := by
  intro hfailure
  exact ay_pcep_disj_right subsumptionFailure
    (AyDisj blockedClauseFailure variableEliminationFailure)
    (ay_pcep_disj_right blockedClauseFailure variableEliminationFailure
      hfailure)

theorem ay_pcep_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (subsumptionFailure : Prop)
    (blockedClauseFailure : Prop)
    (variableEliminationFailure : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticPipelineLogEntry
      previousLog nextLog currentCnf subsumptionFailure
      blockedClauseFailure variableEliminationFailure recompute diagnostic ->
    AyPipelineFailure
      subsumptionFailure blockedClauseFailure variableEliminationFailure := by
  intro entry
  exact ay_pcep_conj_left
    (AyPipelineFailure
      subsumptionFailure blockedClauseFailure variableEliminationFailure)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pcep_conj_left
      (AyConj
        (AyPipelineFailure
          subsumptionFailure blockedClauseFailure variableEliminationFailure)
        (AyConj
          (AyRecomputeObligation currentCnf recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_pcep_conj_right previousLog
        (AyConj
          (AyConj
            (AyPipelineFailure
              subsumptionFailure blockedClauseFailure
              variableEliminationFailure)
            (AyConj
              (AyRecomputeObligation currentCnf recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_pcep_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (subsumptionFailure : Prop)
    (blockedClauseFailure : Prop)
    (variableEliminationFailure : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticPipelineLogEntry
      previousLog nextLog currentCnf subsumptionFailure
      blockedClauseFailure variableEliminationFailure recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_pcep_conj_right
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pcep_conj_right
      (AyPipelineFailure
        subsumptionFailure blockedClauseFailure variableEliminationFailure)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pcep_conj_left
        (AyConj
          (AyPipelineFailure
            subsumptionFailure blockedClauseFailure
            variableEliminationFailure)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pcep_conj_right previousLog
          (AyConj
            (AyConj
              (AyPipelineFailure
                subsumptionFailure blockedClauseFailure
                variableEliminationFailure)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pcep_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (subsumptionFailure : Prop)
    (blockedClauseFailure : Prop)
    (variableEliminationFailure : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticPipelineLogEntry
      previousLog nextLog currentCnf subsumptionFailure
      blockedClauseFailure variableEliminationFailure recompute diagnostic ->
    AyRecomputeObligation currentCnf recompute := by
  intro entry
  exact ay_pcep_conj_left
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pcep_conj_right
      (AyPipelineFailure
        subsumptionFailure blockedClauseFailure variableEliminationFailure)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pcep_conj_left
        (AyConj
          (AyPipelineFailure
            subsumptionFailure blockedClauseFailure
            variableEliminationFailure)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pcep_conj_right previousLog
          (AyConj
            (AyConj
              (AyPipelineFailure
                subsumptionFailure blockedClauseFailure
                variableEliminationFailure)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_preprocess_clause_elimination_pipeline_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (subsumptionFailure : Prop)
    (blockedClauseFailure : Prop)
    (variableEliminationFailure : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticPipelineLogEntry
      previousLog nextLog currentCnf subsumptionFailure
      blockedClauseFailure variableEliminationFailure recompute diagnostic ->
    AyConj
      (AyPipelineFailure
        subsumptionFailure blockedClauseFailure variableEliminationFailure)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_pcep_conj_intro
    (AyPipelineFailure
      subsumptionFailure blockedClauseFailure variableEliminationFailure)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pcep_diagnostic_failure previousLog nextLog currentCnf
      subsumptionFailure blockedClauseFailure variableEliminationFailure
      recompute diagnostic entry)
    (ay_pcep_conj_intro
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pcep_diagnostic_recompute previousLog nextLog currentCnf
        subsumptionFailure blockedClauseFailure variableEliminationFailure
        recompute diagnostic entry)
      (ay_pcep_diagnostic_no_claim previousLog nextLog currentCnf
        subsumptionFailure blockedClauseFailure variableEliminationFailure
        recompute diagnostic entry))
