-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Variable-elimination extension soundness for preprocessing. The
-- propositions stand for bounded resolution witnesses, eliminated-variable
-- extension maps, reconstruction chains, cache keys, accepted reports,
-- diagnostics, and public SAT/UNSAT outcomes.

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

def AyResolutionWitness
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolvents : Prop) :=
  AyConj resolvents (originalCnf -> reducedCnf)

def AyExtensionMap
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (extendedModel : Prop) :=
  AySat reducedCnf reducedModel -> AySat originalCnf extendedModel

def AyReconstructionChain (originalCnf : Prop) (reducedCnf : Prop) :=
  AyEquisat originalCnf reducedCnf

def AyCacheKey
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))

def AyAcceptedExtensionReport
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolvents : Prop) (reducedModel : Prop)
    (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyResolutionWitness originalCnf reducedCnf resolvents)
    (AyConj
      (AyExtensionMap reducedCnf originalCnf reducedModel extendedModel)
      (AyConj
        (AyReconstructionChain originalCnf reducedCnf)
        (AyCacheKey
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))

def AyExtensionFailure
    (missingExtension : Prop) (staleExtension : Prop)
    (badResolution : Prop) (cacheMismatch : Prop) :=
  AyDisj missingExtension
    (AyDisj staleExtension (AyDisj badResolution cacheMismatch))

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  AyConj currentCnf recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedExtensionLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolvents : Prop) (reducedModel : Prop)
    (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedExtensionReport
      originalCnf reducedCnf resolvents reducedModel extendedModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest)
    nextLog

def AyDiagnosticExtensionLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingExtension : Prop) (staleExtension : Prop)
    (badResolution : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyExtensionFailure
        missingExtension staleExtension badResolution cacheMismatch)
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

theorem ay_pvee_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pvee_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pvee_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pvee_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pvee_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pvee_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pvee_conj_left (before -> after) (after -> before) eq

theorem ay_pvee_sat_cnf
    (cnf : Prop) (model : Prop) :
    AySat cnf model ->
    cnf := by
  intro sat
  exact ay_pvee_conj_left cnf model sat

theorem ay_pvee_resolution_resolvents
    (originalCnf : Prop) (reducedCnf : Prop) (resolvents : Prop) :
    AyResolutionWitness originalCnf reducedCnf resolvents ->
    resolvents := by
  intro witness
  exact ay_pvee_conj_left resolvents (originalCnf -> reducedCnf)
    witness

theorem ay_pvee_resolution_forward
    (originalCnf : Prop) (reducedCnf : Prop) (resolvents : Prop) :
    AyResolutionWitness originalCnf reducedCnf resolvents ->
    originalCnf ->
    reducedCnf := by
  intro witness
  exact ay_pvee_conj_right resolvents (originalCnf -> reducedCnf)
    witness

theorem ay_pvee_report_resolution
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolvents : Prop) (reducedModel : Prop)
    (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedExtensionReport
      originalCnf reducedCnf resolvents reducedModel extendedModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyResolutionWitness originalCnf reducedCnf resolvents := by
  intro accepted
  exact ay_pvee_conj_left
    (AyResolutionWitness originalCnf reducedCnf resolvents)
    (AyConj
      (AyExtensionMap reducedCnf originalCnf reducedModel extendedModel)
      (AyConj
        (AyReconstructionChain originalCnf reducedCnf)
        (AyCacheKey
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))
    accepted

theorem ay_pvee_report_extension
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolvents : Prop) (reducedModel : Prop)
    (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedExtensionReport
      originalCnf reducedCnf resolvents reducedModel extendedModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyExtensionMap reducedCnf originalCnf reducedModel extendedModel := by
  intro accepted
  exact ay_pvee_conj_left
    (AyExtensionMap reducedCnf originalCnf reducedModel extendedModel)
    (AyConj
      (AyReconstructionChain originalCnf reducedCnf)
      (AyCacheKey
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))
    (ay_pvee_conj_right
      (AyResolutionWitness originalCnf reducedCnf resolvents)
      (AyConj
        (AyExtensionMap reducedCnf originalCnf reducedModel extendedModel)
        (AyConj
          (AyReconstructionChain originalCnf reducedCnf)
          (AyCacheKey
            cachedEpoch currentEpoch cachedManifest runManifest
            cachedDigest runDigest)))
      accepted)

theorem ay_pvee_report_chain
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolvents : Prop) (reducedModel : Prop)
    (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedExtensionReport
      originalCnf reducedCnf resolvents reducedModel extendedModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyReconstructionChain originalCnf reducedCnf := by
  intro accepted
  exact ay_pvee_conj_left
    (AyReconstructionChain originalCnf reducedCnf)
    (AyCacheKey
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pvee_conj_right
      (AyExtensionMap reducedCnf originalCnf reducedModel extendedModel)
      (AyConj
        (AyReconstructionChain originalCnf reducedCnf)
        (AyCacheKey
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      (ay_pvee_conj_right
        (AyResolutionWitness originalCnf reducedCnf resolvents)
        (AyConj
          (AyExtensionMap reducedCnf originalCnf reducedModel extendedModel)
          (AyConj
            (AyReconstructionChain originalCnf reducedCnf)
            (AyCacheKey
              cachedEpoch currentEpoch cachedManifest runManifest
              cachedDigest runDigest)))
        accepted))

theorem ay_pvee_log_report
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolvents : Prop) (reducedModel : Prop)
    (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedExtensionLogEntry
      previousLog nextLog originalCnf reducedCnf resolvents
      reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyAcceptedExtensionReport
      originalCnf reducedCnf resolvents reducedModel extendedModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest := by
  intro entry
  exact ay_pvee_conj_left
    (AyAcceptedExtensionReport
      originalCnf reducedCnf resolvents reducedModel extendedModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest)
    nextLog
    (ay_pvee_conj_right previousLog
      (AyConj
        (AyAcceptedExtensionReport
          originalCnf reducedCnf resolvents reducedModel extendedModel
          cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
          runDigest)
        nextLog)
      entry)

theorem ay_pvee_extend_sat
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolvents : Prop) (reducedModel : Prop)
    (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedExtensionReport
      originalCnf reducedCnf resolvents reducedModel extendedModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AySat reducedCnf reducedModel ->
    AySat originalCnf extendedModel := by
  intro accepted
  exact ay_pvee_report_extension originalCnf reducedCnf resolvents
    reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
    runManifest cachedDigest runDigest accepted

theorem ay_pvee_unsat_transport
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolvents : Prop) (reducedModel : Prop)
    (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedExtensionReport
      originalCnf reducedCnf resolvents reducedModel extendedModel
      cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
      runDigest ->
    AyReplay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay hcertificate horiginal
  exact replay
    (ay_pvee_equisat_forward originalCnf reducedCnf
      (ay_pvee_report_chain originalCnf reducedCnf resolvents
        reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
        runManifest cachedDigest runDigest accepted)
      horiginal)
    hcertificate

theorem ay_pvee_public_sat_from_extension
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolvents : Prop) (reducedModel : Prop)
    (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedExtensionLogEntry
      previousLog nextLog originalCnf reducedCnf resolvents
      reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AySat reducedCnf reducedModel ->
    exitCode ->
    AyPublicResult originalCnf extendedModel certificate conflict exitCode := by
  intro entry sat hexit
  exact ay_pvee_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf extendedModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pvee_conj_intro exitCode (AySat originalCnf extendedModel)
      hexit
      (ay_pvee_extend_sat originalCnf reducedCnf resolvents reducedModel
        extendedModel cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest
        (ay_pvee_log_report previousLog nextLog originalCnf reducedCnf
          resolvents reducedModel extendedModel cachedEpoch currentEpoch
          cachedManifest runManifest cachedDigest runDigest entry)
        sat))

theorem ay_pvee_public_unsat_from_extension
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (resolvents : Prop) (reducedModel : Prop)
    (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedExtensionLogEntry
      previousLog nextLog originalCnf reducedCnf resolvents
      reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyReplay reducedCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf extendedModel certificate conflict exitCode := by
  intro entry replay hexit
  exact ay_pvee_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf extendedModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pvee_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      (ay_pvee_unsat_transport originalCnf reducedCnf resolvents
        reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
        runManifest cachedDigest runDigest certificate conflict
        (ay_pvee_log_report previousLog nextLog originalCnf reducedCnf
          resolvents reducedModel extendedModel cachedEpoch currentEpoch
          cachedManifest runManifest cachedDigest runDigest entry)
        replay))

theorem ay_pvee_failure_missing
    (missingExtension : Prop) (staleExtension : Prop)
    (badResolution : Prop) (cacheMismatch : Prop) :
    missingExtension ->
    AyExtensionFailure
      missingExtension staleExtension badResolution cacheMismatch := by
  intro hmissing
  exact ay_pvee_disj_left missingExtension
    (AyDisj staleExtension (AyDisj badResolution cacheMismatch))
    hmissing

theorem ay_pvee_failure_stale
    (missingExtension : Prop) (staleExtension : Prop)
    (badResolution : Prop) (cacheMismatch : Prop) :
    staleExtension ->
    AyExtensionFailure
      missingExtension staleExtension badResolution cacheMismatch := by
  intro hstale
  exact ay_pvee_disj_right missingExtension
    (AyDisj staleExtension (AyDisj badResolution cacheMismatch))
    (ay_pvee_disj_left staleExtension
      (AyDisj badResolution cacheMismatch)
      hstale)

theorem ay_pvee_failure_bad_resolution
    (missingExtension : Prop) (staleExtension : Prop)
    (badResolution : Prop) (cacheMismatch : Prop) :
    badResolution ->
    AyExtensionFailure
      missingExtension staleExtension badResolution cacheMismatch := by
  intro hbad
  exact ay_pvee_disj_right missingExtension
    (AyDisj staleExtension (AyDisj badResolution cacheMismatch))
    (ay_pvee_disj_right staleExtension
      (AyDisj badResolution cacheMismatch)
      (ay_pvee_disj_left badResolution cacheMismatch hbad))

theorem ay_pvee_failure_cache_mismatch
    (missingExtension : Prop) (staleExtension : Prop)
    (badResolution : Prop) (cacheMismatch : Prop) :
    cacheMismatch ->
    AyExtensionFailure
      missingExtension staleExtension badResolution cacheMismatch := by
  intro hcache
  exact ay_pvee_disj_right missingExtension
    (AyDisj staleExtension (AyDisj badResolution cacheMismatch))
    (ay_pvee_disj_right staleExtension
      (AyDisj badResolution cacheMismatch)
      (ay_pvee_disj_right badResolution cacheMismatch hcache))

theorem ay_pvee_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingExtension : Prop) (staleExtension : Prop)
    (badResolution : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticExtensionLogEntry
      previousLog nextLog currentCnf missingExtension staleExtension
      badResolution cacheMismatch recompute diagnostic ->
    AyExtensionFailure
      missingExtension staleExtension badResolution cacheMismatch := by
  intro entry
  exact ay_pvee_conj_left
    (AyExtensionFailure
      missingExtension staleExtension badResolution cacheMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pvee_conj_left
      (AyConj
        (AyExtensionFailure
          missingExtension staleExtension badResolution cacheMismatch)
        (AyConj
          (AyRecomputeObligation currentCnf recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_pvee_conj_right previousLog
        (AyConj
          (AyConj
            (AyExtensionFailure
              missingExtension staleExtension badResolution cacheMismatch)
            (AyConj
              (AyRecomputeObligation currentCnf recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_pvee_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingExtension : Prop) (staleExtension : Prop)
    (badResolution : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticExtensionLogEntry
      previousLog nextLog currentCnf missingExtension staleExtension
      badResolution cacheMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_pvee_conj_right
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pvee_conj_right
      (AyExtensionFailure
        missingExtension staleExtension badResolution cacheMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pvee_conj_left
        (AyConj
          (AyExtensionFailure
            missingExtension staleExtension badResolution cacheMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pvee_conj_right previousLog
          (AyConj
            (AyConj
              (AyExtensionFailure
                missingExtension staleExtension badResolution cacheMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pvee_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingExtension : Prop) (staleExtension : Prop)
    (badResolution : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticExtensionLogEntry
      previousLog nextLog currentCnf missingExtension staleExtension
      badResolution cacheMismatch recompute diagnostic ->
    AyRecomputeObligation currentCnf recompute := by
  intro entry
  exact ay_pvee_conj_left
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pvee_conj_right
      (AyExtensionFailure
        missingExtension staleExtension badResolution cacheMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pvee_conj_left
        (AyConj
          (AyExtensionFailure
            missingExtension staleExtension badResolution cacheMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pvee_conj_right previousLog
          (AyConj
            (AyConj
              (AyExtensionFailure
                missingExtension staleExtension badResolution cacheMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pvee_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingExtension : Prop) (staleExtension : Prop)
    (badResolution : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticExtensionLogEntry
      previousLog nextLog currentCnf missingExtension staleExtension
      badResolution cacheMismatch recompute diagnostic ->
    AyConj
      (AyExtensionFailure
        missingExtension staleExtension badResolution cacheMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_pvee_conj_intro
    (AyExtensionFailure
      missingExtension staleExtension badResolution cacheMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pvee_diagnostic_failure previousLog nextLog currentCnf
      missingExtension staleExtension badResolution cacheMismatch
      recompute diagnostic entry)
    (ay_pvee_conj_intro
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pvee_diagnostic_recompute previousLog nextLog currentCnf
        missingExtension staleExtension badResolution cacheMismatch
        recompute diagnostic entry)
      (ay_pvee_diagnostic_no_claim previousLog nextLog currentCnf
        missingExtension staleExtension badResolution cacheMismatch
        recompute diagnostic entry))
