-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Blocked-clause elimination soundness for preprocessing. The propositions
-- stand for original clauses, blocked clauses, elimination witnesses,
-- reconstruction/preprocessing maps, replay witnesses, guard evidence,
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

def AyBlockedClauseWitness
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop) :=
  AyConj
    eliminationWitness
    (originalClauses -> blockedClauses)

def AyReconstructionMap
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  AyConj
    (AySat reducedCnf reducedModel -> AySat originalCnf originalModel)
    (originalCnf -> reducedCnf)

def AyPreprocessMap (originalCnf : Prop) (reducedCnf : Prop) :=
  AyEquisat originalCnf reducedCnf

def AyBlockedClauseGuards
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))

def AyAcceptedBlockedClauseReport
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyPreprocessMap originalCnf reducedCnf)
    (AyConj
      (AyBlockedClauseWitness
        originalClauses blockedClauses eliminationWitness)
      (AyConj
        (AyReconstructionMap
          reducedCnf originalCnf reducedModel originalModel)
        (AyBlockedClauseGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))

def AyBlockedClauseFailure
    (invalidBlocker : Prop) (staleReplay : Prop)
    (digestMismatch : Prop) :=
  AyDisj invalidBlocker (AyDisj staleReplay digestMismatch)

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  AyConj currentCnf recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedBlockedClauseLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedBlockedClauseReport
      originalCnf reducedCnf originalClauses blockedClauses
      eliminationWitness reducedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest)
    nextLog

def AyDiagnosticBlockedClauseLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (invalidBlocker : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyBlockedClauseFailure invalidBlocker staleReplay digestMismatch)
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

theorem ay_pbce_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_pbce_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pbce_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pbce_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft
  intro result
  intro left_case
  intro _right_case
  exact left_case hleft

theorem ay_pbce_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright
  intro result
  intro _left_case
  intro right_case
  exact right_case hright

theorem ay_pbce_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pbce_conj_left (before -> after) (after -> before) eq

theorem ay_pbce_equisat_backward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pbce_conj_right (before -> after) (after -> before) eq

theorem ay_pbce_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_pbce_conj_left cnf model sat

theorem ay_pbce_sat_model
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    model := by
  intro sat
  exact ay_pbce_conj_right cnf model sat

theorem ay_pbce_report_map
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedBlockedClauseReport
      originalCnf reducedCnf originalClauses blockedClauses
      eliminationWitness reducedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyPreprocessMap originalCnf reducedCnf := by
  intro accepted
  exact ay_pbce_conj_left
    (AyPreprocessMap originalCnf reducedCnf)
    (AyConj
      (AyBlockedClauseWitness
        originalClauses blockedClauses eliminationWitness)
      (AyConj
        (AyReconstructionMap
          reducedCnf originalCnf reducedModel originalModel)
        (AyBlockedClauseGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))
    accepted

theorem ay_pbce_report_witness
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedBlockedClauseReport
      originalCnf reducedCnf originalClauses blockedClauses
      eliminationWitness reducedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyBlockedClauseWitness
      originalClauses blockedClauses eliminationWitness := by
  intro accepted
  exact ay_pbce_conj_left
    (AyBlockedClauseWitness originalClauses blockedClauses eliminationWitness)
    (AyConj
      (AyReconstructionMap reducedCnf originalCnf reducedModel originalModel)
      (AyBlockedClauseGuards
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))
    (ay_pbce_conj_right
      (AyPreprocessMap originalCnf reducedCnf)
      (AyConj
        (AyBlockedClauseWitness
          originalClauses blockedClauses eliminationWitness)
        (AyConj
          (AyReconstructionMap
            reducedCnf originalCnf reducedModel originalModel)
          (AyBlockedClauseGuards
            cachedEpoch currentEpoch cachedManifest runManifest
            cachedDigest runDigest)))
      accepted)

theorem ay_pbce_report_reconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedBlockedClauseReport
      originalCnf reducedCnf originalClauses blockedClauses
      eliminationWitness reducedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyReconstructionMap reducedCnf originalCnf reducedModel originalModel := by
  intro accepted
  exact ay_pbce_conj_left
    (AyReconstructionMap reducedCnf originalCnf reducedModel originalModel)
    (AyBlockedClauseGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pbce_conj_right
      (AyBlockedClauseWitness originalClauses blockedClauses eliminationWitness)
      (AyConj
        (AyReconstructionMap
          reducedCnf originalCnf reducedModel originalModel)
        (AyBlockedClauseGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      (ay_pbce_conj_right
        (AyPreprocessMap originalCnf reducedCnf)
        (AyConj
          (AyBlockedClauseWitness
            originalClauses blockedClauses eliminationWitness)
          (AyConj
            (AyReconstructionMap
              reducedCnf originalCnf reducedModel originalModel)
            (AyBlockedClauseGuards
              cachedEpoch currentEpoch cachedManifest runManifest
              cachedDigest runDigest)))
        accepted))

theorem ay_pbce_report_guards
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedBlockedClauseReport
      originalCnf reducedCnf originalClauses blockedClauses
      eliminationWitness reducedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyBlockedClauseGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest := by
  intro accepted
  exact ay_pbce_conj_right
    (AyReconstructionMap reducedCnf originalCnf reducedModel originalModel)
    (AyBlockedClauseGuards
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pbce_conj_right
      (AyBlockedClauseWitness originalClauses blockedClauses eliminationWitness)
      (AyConj
        (AyReconstructionMap
          reducedCnf originalCnf reducedModel originalModel)
        (AyBlockedClauseGuards
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      (ay_pbce_conj_right
        (AyPreprocessMap originalCnf reducedCnf)
        (AyConj
          (AyBlockedClauseWitness
            originalClauses blockedClauses eliminationWitness)
          (AyConj
            (AyReconstructionMap
              reducedCnf originalCnf reducedModel originalModel)
            (AyBlockedClauseGuards
              cachedEpoch currentEpoch cachedManifest runManifest
              cachedDigest runDigest)))
        accepted))

theorem ay_pbce_witness_token
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop) :
    AyBlockedClauseWitness
      originalClauses blockedClauses eliminationWitness ->
    eliminationWitness := by
  intro witness
  exact ay_pbce_conj_left eliminationWitness
    (originalClauses -> blockedClauses)
    witness

theorem ay_pbce_blocked_from_original
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop) :
    AyBlockedClauseWitness
      originalClauses blockedClauses eliminationWitness ->
    originalClauses ->
    blockedClauses := by
  intro witness
  exact ay_pbce_conj_right eliminationWitness
    (originalClauses -> blockedClauses)
    witness

theorem ay_pbce_reconstruct_sat
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    AyReconstructionMap reducedCnf originalCnf reducedModel originalModel ->
    AySat reducedCnf reducedModel ->
    AySat originalCnf originalModel := by
  intro reconstruction
  exact ay_pbce_conj_left
    (AySat reducedCnf reducedModel -> AySat originalCnf originalModel)
    (originalCnf -> reducedCnf)
    reconstruction

theorem ay_pbce_original_to_reduced
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    AyReconstructionMap reducedCnf originalCnf reducedModel originalModel ->
    originalCnf ->
    reducedCnf := by
  intro reconstruction
  exact ay_pbce_conj_right
    (AySat reducedCnf reducedModel -> AySat originalCnf originalModel)
    (originalCnf -> reducedCnf)
    reconstruction

theorem ay_pbce_accepted_semantics
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedBlockedClauseReport
      originalCnf reducedCnf originalClauses blockedClauses
      eliminationWitness reducedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyEquisat originalCnf reducedCnf := by
  intro accepted
  exact ay_pbce_report_map originalCnf reducedCnf originalClauses
    blockedClauses eliminationWitness reducedModel originalModel
    cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
    runDigest accepted

theorem ay_pbce_sat_reconstruct_from_reduced
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedBlockedClauseReport
      originalCnf reducedCnf originalClauses blockedClauses
      eliminationWitness reducedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AySat reducedCnf reducedModel ->
    AySat originalCnf originalModel := by
  intro accepted
  exact ay_pbce_reconstruct_sat reducedCnf originalCnf
    reducedModel originalModel
    (ay_pbce_report_reconstruction originalCnf reducedCnf originalClauses
      blockedClauses eliminationWitness reducedModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest accepted)

theorem ay_pbce_sat_forward_to_reduced
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedBlockedClauseReport
      originalCnf reducedCnf originalClauses blockedClauses
      eliminationWitness reducedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    originalCnf ->
    reducedCnf := by
  intro accepted
  exact ay_pbce_equisat_forward originalCnf reducedCnf
    (ay_pbce_accepted_semantics originalCnf reducedCnf originalClauses
      blockedClauses eliminationWitness reducedModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest accepted)

theorem ay_pbce_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedBlockedClauseReport
      originalCnf reducedCnf originalClauses blockedClauses
      eliminationWitness reducedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest ->
    AyReplay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted
  intro replay
  intro hcertificate
  intro horiginal
  exact replay
    (ay_pbce_sat_forward_to_reduced originalCnf reducedCnf
      originalClauses blockedClauses eliminationWitness reducedModel
      originalModel cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest accepted horiginal)
    hcertificate

theorem ay_pbce_accepted_log_report
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedBlockedClauseLogEntry
      previousLog nextLog originalCnf reducedCnf originalClauses
      blockedClauses eliminationWitness reducedModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyAcceptedBlockedClauseReport
      originalCnf reducedCnf originalClauses blockedClauses
      eliminationWitness reducedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest := by
  intro entry
  exact ay_pbce_conj_left
    (AyAcceptedBlockedClauseReport
      originalCnf reducedCnf originalClauses blockedClauses
      eliminationWitness reducedModel originalModel cachedEpoch
      currentEpoch cachedManifest runManifest cachedDigest runDigest)
    nextLog
    (ay_pbce_conj_right previousLog
      (AyConj
        (AyAcceptedBlockedClauseReport
          originalCnf reducedCnf originalClauses blockedClauses
          eliminationWitness reducedModel originalModel cachedEpoch
          currentEpoch cachedManifest runManifest cachedDigest runDigest)
        nextLog)
      entry)

theorem ay_pbce_accepted_log_append_only
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedBlockedClauseLogEntry
      previousLog nextLog originalCnf reducedCnf originalClauses
      blockedClauses eliminationWitness reducedModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyConj previousLog nextLog := by
  intro entry
  exact ay_pbce_conj_intro previousLog nextLog
    (ay_pbce_conj_left previousLog
      (AyConj
        (AyAcceptedBlockedClauseReport
          originalCnf reducedCnf originalClauses blockedClauses
          eliminationWitness reducedModel originalModel cachedEpoch
          currentEpoch cachedManifest runManifest cachedDigest runDigest)
        nextLog)
      entry)
    (ay_pbce_conj_right
      (AyAcceptedBlockedClauseReport
        originalCnf reducedCnf originalClauses blockedClauses
        eliminationWitness reducedModel originalModel cachedEpoch
        currentEpoch cachedManifest runManifest cachedDigest runDigest)
      nextLog
      (ay_pbce_conj_right previousLog
        (AyConj
          (AyAcceptedBlockedClauseReport
            originalCnf reducedCnf originalClauses blockedClauses
            eliminationWitness reducedModel originalModel cachedEpoch
            currentEpoch cachedManifest runManifest cachedDigest runDigest)
          nextLog)
        entry))

theorem ay_pbce_public_sat_from_reduced
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedBlockedClauseLogEntry
      previousLog nextLog originalCnf reducedCnf originalClauses
      blockedClauses eliminationWitness reducedModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AySat reducedCnf reducedModel ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry
  intro sat
  intro hexit
  exact ay_pbce_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pbce_conj_intro exitCode (AySat originalCnf originalModel)
      hexit
      (ay_pbce_sat_reconstruct_from_reduced originalCnf reducedCnf
        originalClauses blockedClauses eliminationWitness reducedModel
        originalModel cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest
        (ay_pbce_accepted_log_report previousLog nextLog originalCnf
          reducedCnf originalClauses blockedClauses eliminationWitness
          reducedModel originalModel cachedEpoch currentEpoch
          cachedManifest runManifest cachedDigest runDigest entry)
        sat))

theorem ay_pbce_public_unsat_from_reduced
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (originalClauses : Prop) (blockedClauses : Prop)
    (eliminationWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedBlockedClauseLogEntry
      previousLog nextLog originalCnf reducedCnf originalClauses
      blockedClauses eliminationWitness reducedModel originalModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyReplay reducedCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry
  intro replay
  intro hexit
  exact ay_pbce_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pbce_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      (ay_pbce_unsat_pushback originalCnf reducedCnf originalClauses
        blockedClauses eliminationWitness reducedModel originalModel
        cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
        runDigest certificate conflict
        (ay_pbce_accepted_log_report previousLog nextLog originalCnf
          reducedCnf originalClauses blockedClauses eliminationWitness
          reducedModel originalModel cachedEpoch currentEpoch
          cachedManifest runManifest cachedDigest runDigest entry)
        replay))

theorem ay_pbce_failure_invalid_blocker
    (invalidBlocker : Prop) (staleReplay : Prop)
    (digestMismatch : Prop) :
    invalidBlocker ->
    AyBlockedClauseFailure invalidBlocker staleReplay digestMismatch := by
  intro hinvalid
  exact ay_pbce_disj_left invalidBlocker
    (AyDisj staleReplay digestMismatch)
    hinvalid

theorem ay_pbce_failure_stale_replay
    (invalidBlocker : Prop) (staleReplay : Prop)
    (digestMismatch : Prop) :
    staleReplay ->
    AyBlockedClauseFailure invalidBlocker staleReplay digestMismatch := by
  intro hstale
  exact ay_pbce_disj_right invalidBlocker
    (AyDisj staleReplay digestMismatch)
    (ay_pbce_disj_left staleReplay digestMismatch hstale)

theorem ay_pbce_failure_digest_mismatch
    (invalidBlocker : Prop) (staleReplay : Prop)
    (digestMismatch : Prop) :
    digestMismatch ->
    AyBlockedClauseFailure invalidBlocker staleReplay digestMismatch := by
  intro hdigest
  exact ay_pbce_disj_right invalidBlocker
    (AyDisj staleReplay digestMismatch)
    (ay_pbce_disj_right staleReplay digestMismatch hdigest)

theorem ay_pbce_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (invalidBlocker : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticBlockedClauseLogEntry
      previousLog nextLog currentCnf invalidBlocker staleReplay
      digestMismatch recompute diagnostic ->
    AyBlockedClauseFailure invalidBlocker staleReplay digestMismatch := by
  intro entry
  exact ay_pbce_conj_left
    (AyBlockedClauseFailure invalidBlocker staleReplay digestMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pbce_conj_left
      (AyConj
        (AyBlockedClauseFailure invalidBlocker staleReplay digestMismatch)
        (AyConj
          (AyRecomputeObligation currentCnf recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_pbce_conj_right previousLog
        (AyConj
          (AyConj
            (AyBlockedClauseFailure
              invalidBlocker staleReplay digestMismatch)
            (AyConj
              (AyRecomputeObligation currentCnf recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_pbce_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (invalidBlocker : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticBlockedClauseLogEntry
      previousLog nextLog currentCnf invalidBlocker staleReplay
      digestMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_pbce_conj_right
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pbce_conj_right
      (AyBlockedClauseFailure invalidBlocker staleReplay digestMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pbce_conj_left
        (AyConj
          (AyBlockedClauseFailure invalidBlocker staleReplay digestMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pbce_conj_right previousLog
          (AyConj
            (AyConj
              (AyBlockedClauseFailure
                invalidBlocker staleReplay digestMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pbce_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (invalidBlocker : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticBlockedClauseLogEntry
      previousLog nextLog currentCnf invalidBlocker staleReplay
      digestMismatch recompute diagnostic ->
    AyRecomputeObligation currentCnf recompute := by
  intro entry
  exact ay_pbce_conj_left
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pbce_conj_right
      (AyBlockedClauseFailure invalidBlocker staleReplay digestMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pbce_conj_left
        (AyConj
          (AyBlockedClauseFailure invalidBlocker staleReplay digestMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pbce_conj_right previousLog
          (AyConj
            (AyConj
              (AyBlockedClauseFailure
                invalidBlocker staleReplay digestMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_preprocess_blocked_clause_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (invalidBlocker : Prop) (staleReplay : Prop)
    (digestMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticBlockedClauseLogEntry
      previousLog nextLog currentCnf invalidBlocker staleReplay
      digestMismatch recompute diagnostic ->
    AyConj
      (AyBlockedClauseFailure invalidBlocker staleReplay digestMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_pbce_conj_intro
    (AyBlockedClauseFailure invalidBlocker staleReplay digestMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pbce_diagnostic_failure previousLog nextLog currentCnf
      invalidBlocker staleReplay digestMismatch recompute diagnostic entry)
    (ay_pbce_conj_intro
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pbce_diagnostic_recompute previousLog nextLog currentCnf
        invalidBlocker staleReplay digestMismatch recompute diagnostic entry)
      (ay_pbce_diagnostic_no_claim previousLog nextLog currentCnf
        invalidBlocker staleReplay digestMismatch recompute diagnostic entry))
