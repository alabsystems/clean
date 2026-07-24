-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Cache-gated subsumption/SSR/vivification/elimination soundness. The
-- propositions stand for stage certificates, reconstruction maps, cache keys,
-- accepted reports, stale/missing/mismatched diagnostics, and public SAT/UNSAT
-- outcomes for ay preprocessing.

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

def AyStageCertificate
    (inputCnf : Prop) (outputCnf : Prop) (stageWitness : Prop) :=
  AyConj stageWitness (AyEquisat inputCnf outputCnf)

def AySubsumptionVivificationChain
    (originalCnf : Prop) (subsumedCnf : Prop) (ssrCnf : Prop)
    (vivifiedCnf : Prop) (eliminatedCnf : Prop)
    (subsumptionCert : Prop) (ssrCert : Prop)
    (vivificationCert : Prop) (eliminationCert : Prop) :=
  AyConj
    (AyStageCertificate originalCnf subsumedCnf subsumptionCert)
    (AyConj
      (AyStageCertificate subsumedCnf ssrCnf ssrCert)
      (AyConj
        (AyStageCertificate ssrCnf vivifiedCnf vivificationCert)
        (AyStageCertificate vivifiedCnf eliminatedCnf eliminationCert)))

def AyReconstructionMap
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :=
  AyConj
    (AySat finalCnf finalModel -> AySat originalCnf originalModel)
    (originalCnf -> finalCnf)

def AyCacheKey
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))

def AyAcceptedGateReport
    (originalCnf : Prop) (subsumedCnf : Prop) (ssrCnf : Prop)
    (vivifiedCnf : Prop) (eliminatedCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (subsumptionCert : Prop) (ssrCert : Prop)
    (vivificationCert : Prop) (eliminationCert : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AySubsumptionVivificationChain
      originalCnf subsumedCnf ssrCnf vivifiedCnf eliminatedCnf
      subsumptionCert ssrCert vivificationCert eliminationCert)
    (AyConj
      (AyReconstructionMap
        eliminatedCnf originalCnf finalModel originalModel)
      (AyCacheKey
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))

def AyGateFailure
    (missingCertificate : Prop) (staleCertificate : Prop)
    (stageMismatch : Prop) (cacheMismatch : Prop) :=
  AyDisj missingCertificate
    (AyDisj staleCertificate (AyDisj stageMismatch cacheMismatch))

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  AyConj currentCnf recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedGateLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (subsumedCnf : Prop) (ssrCnf : Prop)
    (vivifiedCnf : Prop) (eliminatedCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (subsumptionCert : Prop) (ssrCert : Prop)
    (vivificationCert : Prop) (eliminationCert : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedGateReport
      originalCnf subsumedCnf ssrCnf vivifiedCnf eliminatedCnf
      finalModel originalModel subsumptionCert ssrCert vivificationCert
      eliminationCert cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    nextLog

def AyDiagnosticGateLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingCertificate : Prop) (staleCertificate : Prop)
    (stageMismatch : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyGateFailure
        missingCertificate staleCertificate stageMismatch cacheMismatch)
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

theorem ay_psvg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_psvg_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_psvg_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_psvg_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_psvg_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_psvg_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_psvg_conj_left (before -> after) (after -> before) eq

theorem ay_psvg_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_psvg_conj_left cnf model sat

theorem ay_psvg_stage_witness
    (inputCnf : Prop) (outputCnf : Prop) (stageWitness : Prop) :
    AyStageCertificate inputCnf outputCnf stageWitness ->
    stageWitness := by
  intro cert
  exact ay_psvg_conj_left stageWitness
    (AyEquisat inputCnf outputCnf)
    cert

theorem ay_psvg_stage_semantics
    (inputCnf : Prop) (outputCnf : Prop) (stageWitness : Prop) :
    AyStageCertificate inputCnf outputCnf stageWitness ->
    AyEquisat inputCnf outputCnf := by
  intro cert
  exact ay_psvg_conj_right stageWitness
    (AyEquisat inputCnf outputCnf)
    cert

theorem ay_psvg_report_chain
    (originalCnf : Prop) (subsumedCnf : Prop) (ssrCnf : Prop)
    (vivifiedCnf : Prop) (eliminatedCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (subsumptionCert : Prop) (ssrCert : Prop)
    (vivificationCert : Prop) (eliminationCert : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedGateReport
      originalCnf subsumedCnf ssrCnf vivifiedCnf eliminatedCnf
      finalModel originalModel subsumptionCert ssrCert vivificationCert
      eliminationCert cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AySubsumptionVivificationChain
      originalCnf subsumedCnf ssrCnf vivifiedCnf eliminatedCnf
      subsumptionCert ssrCert vivificationCert eliminationCert := by
  intro accepted
  exact ay_psvg_conj_left
    (AySubsumptionVivificationChain
      originalCnf subsumedCnf ssrCnf vivifiedCnf eliminatedCnf
      subsumptionCert ssrCert vivificationCert eliminationCert)
    (AyConj
      (AyReconstructionMap
        eliminatedCnf originalCnf finalModel originalModel)
      (AyCacheKey
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))
    accepted

theorem ay_psvg_report_reconstruction
    (originalCnf : Prop) (subsumedCnf : Prop) (ssrCnf : Prop)
    (vivifiedCnf : Prop) (eliminatedCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (subsumptionCert : Prop) (ssrCert : Prop)
    (vivificationCert : Prop) (eliminationCert : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedGateReport
      originalCnf subsumedCnf ssrCnf vivifiedCnf eliminatedCnf
      finalModel originalModel subsumptionCert ssrCert vivificationCert
      eliminationCert cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest ->
    AyReconstructionMap eliminatedCnf originalCnf finalModel originalModel := by
  intro accepted
  exact ay_psvg_conj_left
    (AyReconstructionMap eliminatedCnf originalCnf finalModel originalModel)
    (AyCacheKey
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_psvg_conj_right
      (AySubsumptionVivificationChain
        originalCnf subsumedCnf ssrCnf vivifiedCnf eliminatedCnf
        subsumptionCert ssrCert vivificationCert eliminationCert)
      (AyConj
        (AyReconstructionMap
          eliminatedCnf originalCnf finalModel originalModel)
        (AyCacheKey
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      accepted)

theorem ay_psvg_chain_original_to_final
    (originalCnf : Prop) (subsumedCnf : Prop) (ssrCnf : Prop)
    (vivifiedCnf : Prop) (eliminatedCnf : Prop)
    (subsumptionCert : Prop) (ssrCert : Prop)
    (vivificationCert : Prop) (eliminationCert : Prop) :
    AySubsumptionVivificationChain
      originalCnf subsumedCnf ssrCnf vivifiedCnf eliminatedCnf
      subsumptionCert ssrCert vivificationCert eliminationCert ->
    originalCnf ->
    eliminatedCnf := by
  intro chain horiginal
  have hsub : AyStageCertificate originalCnf subsumedCnf subsumptionCert :=
    ay_psvg_conj_left
      (AyStageCertificate originalCnf subsumedCnf subsumptionCert)
      (AyConj
        (AyStageCertificate subsumedCnf ssrCnf ssrCert)
        (AyConj
          (AyStageCertificate ssrCnf vivifiedCnf vivificationCert)
          (AyStageCertificate vivifiedCnf eliminatedCnf eliminationCert)))
      chain
  have rest :
      AyConj
        (AyStageCertificate subsumedCnf ssrCnf ssrCert)
        (AyConj
          (AyStageCertificate ssrCnf vivifiedCnf vivificationCert)
          (AyStageCertificate vivifiedCnf eliminatedCnf eliminationCert)) :=
    ay_psvg_conj_right
      (AyStageCertificate originalCnf subsumedCnf subsumptionCert)
      (AyConj
        (AyStageCertificate subsumedCnf ssrCnf ssrCert)
        (AyConj
          (AyStageCertificate ssrCnf vivifiedCnf vivificationCert)
          (AyStageCertificate vivifiedCnf eliminatedCnf eliminationCert)))
      chain
  have hssr : AyStageCertificate subsumedCnf ssrCnf ssrCert :=
    ay_psvg_conj_left
      (AyStageCertificate subsumedCnf ssrCnf ssrCert)
      (AyConj
        (AyStageCertificate ssrCnf vivifiedCnf vivificationCert)
        (AyStageCertificate vivifiedCnf eliminatedCnf eliminationCert))
      rest
  have tail :
      AyConj
        (AyStageCertificate ssrCnf vivifiedCnf vivificationCert)
        (AyStageCertificate vivifiedCnf eliminatedCnf eliminationCert) :=
    ay_psvg_conj_right
      (AyStageCertificate subsumedCnf ssrCnf ssrCert)
      (AyConj
        (AyStageCertificate ssrCnf vivifiedCnf vivificationCert)
        (AyStageCertificate vivifiedCnf eliminatedCnf eliminationCert))
      rest
  have hviv : AyStageCertificate ssrCnf vivifiedCnf vivificationCert :=
    ay_psvg_conj_left
      (AyStageCertificate ssrCnf vivifiedCnf vivificationCert)
      (AyStageCertificate vivifiedCnf eliminatedCnf eliminationCert)
      tail
  have helim : AyStageCertificate vivifiedCnf eliminatedCnf eliminationCert :=
    ay_psvg_conj_right
      (AyStageCertificate ssrCnf vivifiedCnf vivificationCert)
      (AyStageCertificate vivifiedCnf eliminatedCnf eliminationCert)
      tail
  exact ay_psvg_equisat_forward vivifiedCnf eliminatedCnf
    (ay_psvg_stage_semantics vivifiedCnf eliminatedCnf
      eliminationCert helim)
    (ay_psvg_equisat_forward ssrCnf vivifiedCnf
      (ay_psvg_stage_semantics ssrCnf vivifiedCnf
        vivificationCert hviv)
      (ay_psvg_equisat_forward subsumedCnf ssrCnf
        (ay_psvg_stage_semantics subsumedCnf ssrCnf ssrCert hssr)
        (ay_psvg_equisat_forward originalCnf subsumedCnf
          (ay_psvg_stage_semantics originalCnf subsumedCnf
            subsumptionCert hsub)
          horiginal)))

theorem ay_psvg_reconstruct_sat
    (finalCnf : Prop) (originalCnf : Prop)
    (finalModel : Prop) (originalModel : Prop) :
    AyReconstructionMap finalCnf originalCnf finalModel originalModel ->
    AySat finalCnf finalModel ->
    AySat originalCnf originalModel := by
  intro reconstruction
  exact ay_psvg_conj_left
    (AySat finalCnf finalModel -> AySat originalCnf originalModel)
    (originalCnf -> finalCnf)
    reconstruction

theorem ay_psvg_log_report
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (subsumedCnf : Prop) (ssrCnf : Prop)
    (vivifiedCnf : Prop) (eliminatedCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (subsumptionCert : Prop) (ssrCert : Prop)
    (vivificationCert : Prop) (eliminationCert : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedGateLogEntry
      previousLog nextLog originalCnf subsumedCnf ssrCnf vivifiedCnf
      eliminatedCnf finalModel originalModel subsumptionCert ssrCert
      vivificationCert eliminationCert cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AyAcceptedGateReport
      originalCnf subsumedCnf ssrCnf vivifiedCnf eliminatedCnf
      finalModel originalModel subsumptionCert ssrCert vivificationCert
      eliminationCert cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest := by
  intro entry
  exact ay_psvg_conj_left
    (AyAcceptedGateReport
      originalCnf subsumedCnf ssrCnf vivifiedCnf eliminatedCnf
      finalModel originalModel subsumptionCert ssrCert vivificationCert
      eliminationCert cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    nextLog
    (ay_psvg_conj_right previousLog
      (AyConj
        (AyAcceptedGateReport
          originalCnf subsumedCnf ssrCnf vivifiedCnf eliminatedCnf
          finalModel originalModel subsumptionCert ssrCert vivificationCert
          eliminationCert cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)
        nextLog)
      entry)

theorem ay_psvg_public_sat_from_gate
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (subsumedCnf : Prop) (ssrCnf : Prop)
    (vivifiedCnf : Prop) (eliminatedCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (subsumptionCert : Prop) (ssrCert : Prop)
    (vivificationCert : Prop) (eliminationCert : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedGateLogEntry
      previousLog nextLog originalCnf subsumedCnf ssrCnf vivifiedCnf
      eliminatedCnf finalModel originalModel subsumptionCert ssrCert
      vivificationCert eliminationCert cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AySat eliminatedCnf finalModel ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry sat hexit
  exact ay_psvg_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_psvg_conj_intro exitCode (AySat originalCnf originalModel)
      hexit
      (ay_psvg_reconstruct_sat eliminatedCnf originalCnf
        finalModel originalModel
        (ay_psvg_report_reconstruction originalCnf subsumedCnf ssrCnf
          vivifiedCnf eliminatedCnf finalModel originalModel
          subsumptionCert ssrCert vivificationCert eliminationCert
          cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
          runDigest
          (ay_psvg_log_report previousLog nextLog originalCnf
            subsumedCnf ssrCnf vivifiedCnf eliminatedCnf finalModel
            originalModel subsumptionCert ssrCert vivificationCert
            eliminationCert cachedEpoch currentEpoch cachedManifest
            runManifest cachedDigest runDigest entry))
        sat))

theorem ay_psvg_public_unsat_from_gate
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (subsumedCnf : Prop) (ssrCnf : Prop)
    (vivifiedCnf : Prop) (eliminatedCnf : Prop)
    (finalModel : Prop) (originalModel : Prop)
    (subsumptionCert : Prop) (ssrCert : Prop)
    (vivificationCert : Prop) (eliminationCert : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedGateLogEntry
      previousLog nextLog originalCnf subsumedCnf ssrCnf vivifiedCnf
      eliminatedCnf finalModel originalModel subsumptionCert ssrCert
      vivificationCert eliminationCert cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AyReplay eliminatedCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry replay hexit
  exact ay_psvg_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_psvg_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      (fun hcertificate horiginal =>
        replay
          (ay_psvg_chain_original_to_final originalCnf subsumedCnf ssrCnf
            vivifiedCnf eliminatedCnf subsumptionCert ssrCert
            vivificationCert eliminationCert
            (ay_psvg_report_chain originalCnf subsumedCnf ssrCnf
              vivifiedCnf eliminatedCnf finalModel originalModel
              subsumptionCert ssrCert vivificationCert eliminationCert
              cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
              runDigest
              (ay_psvg_log_report previousLog nextLog originalCnf
                subsumedCnf ssrCnf vivifiedCnf eliminatedCnf finalModel
                originalModel subsumptionCert ssrCert vivificationCert
                eliminationCert cachedEpoch currentEpoch cachedManifest
                runManifest cachedDigest runDigest entry))
            horiginal)
          hcertificate))

theorem ay_psvg_failure_missing
    (missingCertificate : Prop) (staleCertificate : Prop)
    (stageMismatch : Prop) (cacheMismatch : Prop) :
    missingCertificate ->
    AyGateFailure
      missingCertificate staleCertificate stageMismatch cacheMismatch := by
  intro hmissing
  exact ay_psvg_disj_left missingCertificate
    (AyDisj staleCertificate (AyDisj stageMismatch cacheMismatch))
    hmissing

theorem ay_psvg_failure_stale
    (missingCertificate : Prop) (staleCertificate : Prop)
    (stageMismatch : Prop) (cacheMismatch : Prop) :
    staleCertificate ->
    AyGateFailure
      missingCertificate staleCertificate stageMismatch cacheMismatch := by
  intro hstale
  exact ay_psvg_disj_right missingCertificate
    (AyDisj staleCertificate (AyDisj stageMismatch cacheMismatch))
    (ay_psvg_disj_left staleCertificate
      (AyDisj stageMismatch cacheMismatch)
      hstale)

theorem ay_psvg_failure_stage_mismatch
    (missingCertificate : Prop) (staleCertificate : Prop)
    (stageMismatch : Prop) (cacheMismatch : Prop) :
    stageMismatch ->
    AyGateFailure
      missingCertificate staleCertificate stageMismatch cacheMismatch := by
  intro hstage
  exact ay_psvg_disj_right missingCertificate
    (AyDisj staleCertificate (AyDisj stageMismatch cacheMismatch))
    (ay_psvg_disj_right staleCertificate
      (AyDisj stageMismatch cacheMismatch)
      (ay_psvg_disj_left stageMismatch cacheMismatch hstage))

theorem ay_psvg_failure_cache_mismatch
    (missingCertificate : Prop) (staleCertificate : Prop)
    (stageMismatch : Prop) (cacheMismatch : Prop) :
    cacheMismatch ->
    AyGateFailure
      missingCertificate staleCertificate stageMismatch cacheMismatch := by
  intro hcache
  exact ay_psvg_disj_right missingCertificate
    (AyDisj staleCertificate (AyDisj stageMismatch cacheMismatch))
    (ay_psvg_disj_right staleCertificate
      (AyDisj stageMismatch cacheMismatch)
      (ay_psvg_disj_right stageMismatch cacheMismatch hcache))

theorem ay_psvg_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingCertificate : Prop) (staleCertificate : Prop)
    (stageMismatch : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticGateLogEntry
      previousLog nextLog currentCnf missingCertificate staleCertificate
      stageMismatch cacheMismatch recompute diagnostic ->
    AyGateFailure
      missingCertificate staleCertificate stageMismatch cacheMismatch := by
  intro entry
  exact ay_psvg_conj_left
    (AyGateFailure
      missingCertificate staleCertificate stageMismatch cacheMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_psvg_conj_left
      (AyConj
        (AyGateFailure
          missingCertificate staleCertificate stageMismatch cacheMismatch)
        (AyConj
          (AyRecomputeObligation currentCnf recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_psvg_conj_right previousLog
        (AyConj
          (AyConj
            (AyGateFailure
              missingCertificate staleCertificate stageMismatch cacheMismatch)
            (AyConj
              (AyRecomputeObligation currentCnf recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_psvg_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingCertificate : Prop) (staleCertificate : Prop)
    (stageMismatch : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticGateLogEntry
      previousLog nextLog currentCnf missingCertificate staleCertificate
      stageMismatch cacheMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_psvg_conj_right
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_psvg_conj_right
      (AyGateFailure
        missingCertificate staleCertificate stageMismatch cacheMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_psvg_conj_left
        (AyConj
          (AyGateFailure
            missingCertificate staleCertificate stageMismatch cacheMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_psvg_conj_right previousLog
          (AyConj
            (AyConj
              (AyGateFailure
                missingCertificate staleCertificate stageMismatch cacheMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_psvg_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingCertificate : Prop) (staleCertificate : Prop)
    (stageMismatch : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticGateLogEntry
      previousLog nextLog currentCnf missingCertificate staleCertificate
      stageMismatch cacheMismatch recompute diagnostic ->
    AyRecomputeObligation currentCnf recompute := by
  intro entry
  exact ay_psvg_conj_left
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_psvg_conj_right
      (AyGateFailure
        missingCertificate staleCertificate stageMismatch cacheMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_psvg_conj_left
        (AyConj
          (AyGateFailure
            missingCertificate staleCertificate stageMismatch cacheMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_psvg_conj_right previousLog
          (AyConj
            (AyConj
              (AyGateFailure
                missingCertificate staleCertificate stageMismatch cacheMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_psvg_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingCertificate : Prop) (staleCertificate : Prop)
    (stageMismatch : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticGateLogEntry
      previousLog nextLog currentCnf missingCertificate staleCertificate
      stageMismatch cacheMismatch recompute diagnostic ->
    AyConj
      (AyGateFailure
        missingCertificate staleCertificate stageMismatch cacheMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_psvg_conj_intro
    (AyGateFailure
      missingCertificate staleCertificate stageMismatch cacheMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_psvg_diagnostic_failure previousLog nextLog currentCnf
      missingCertificate staleCertificate stageMismatch cacheMismatch
      recompute diagnostic entry)
    (ay_psvg_conj_intro
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_psvg_diagnostic_recompute previousLog nextLog currentCnf
        missingCertificate staleCertificate stageMismatch cacheMismatch
        recompute diagnostic entry)
      (ay_psvg_diagnostic_no_claim previousLog nextLog currentCnf
        missingCertificate staleCertificate stageMismatch cacheMismatch
        recompute diagnostic entry))
