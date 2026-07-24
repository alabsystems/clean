-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Pure-literal elimination certificate soundness. The propositions stand for
-- purity certificates, assignment-extension evidence, reconstruction/equisat
-- chains, cache/digest agreement, diagnostics, and public SAT/UNSAT outcomes.

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

def AyPurityCertificate
    (pureLiterals : Prop) (polarityWitness : Prop) :=
  AyConj pureLiterals polarityWitness

def AyAssignmentExtension
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (extendedModel : Prop) :=
  AySat reducedCnf reducedModel -> AySat originalCnf extendedModel

def AyPureLiteralStep
    (originalCnf : Prop) (reducedCnf : Prop)
    (pureLiterals : Prop) (polarityWitness : Prop) :=
  AyConj
    (AyPurityCertificate pureLiterals polarityWitness)
    (originalCnf -> reducedCnf)

def AyReconstructionChain (originalCnf : Prop) (reducedCnf : Prop) :=
  AyEquisat originalCnf reducedCnf

def AyCacheEvidence
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))

def AyAcceptedPureLiteralReport
    (originalCnf : Prop) (reducedCnf : Prop)
    (pureLiterals : Prop) (polarityWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyPureLiteralStep
      originalCnf reducedCnf pureLiterals polarityWitness)
    (AyConj
      (AyAssignmentExtension
        reducedCnf originalCnf reducedModel extendedModel)
      (AyConj
        (AyReconstructionChain originalCnf reducedCnf)
        (AyCacheEvidence
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))

def AyPureLiteralFailure
    (missingPurity : Prop) (stalePurity : Prop)
    (badPolarity : Prop) (cacheMismatch : Prop) :=
  AyDisj missingPurity
    (AyDisj stalePurity (AyDisj badPolarity cacheMismatch))

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  AyConj currentCnf recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedPureLiteralLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (pureLiterals : Prop) (polarityWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedPureLiteralReport
      originalCnf reducedCnf pureLiterals polarityWitness
      reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest)
    nextLog

def AyDiagnosticPureLiteralLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingPurity : Prop) (stalePurity : Prop)
    (badPolarity : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyPureLiteralFailure
        missingPurity stalePurity badPolarity cacheMismatch)
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

theorem ay_pplc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pplc_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pplc_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pplc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pplc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pplc_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pplc_conj_left (before -> after) (after -> before) eq

theorem ay_pplc_purity_literals
    (pureLiterals : Prop) (polarityWitness : Prop) :
    AyPurityCertificate pureLiterals polarityWitness ->
    pureLiterals := by
  intro cert
  exact ay_pplc_conj_left pureLiterals polarityWitness cert

theorem ay_pplc_purity_polarity
    (pureLiterals : Prop) (polarityWitness : Prop) :
    AyPurityCertificate pureLiterals polarityWitness ->
    polarityWitness := by
  intro cert
  exact ay_pplc_conj_right pureLiterals polarityWitness cert

theorem ay_pplc_step_certificate
    (originalCnf : Prop) (reducedCnf : Prop)
    (pureLiterals : Prop) (polarityWitness : Prop) :
    AyPureLiteralStep
      originalCnf reducedCnf pureLiterals polarityWitness ->
    AyPurityCertificate pureLiterals polarityWitness := by
  intro step
  exact ay_pplc_conj_left
    (AyPurityCertificate pureLiterals polarityWitness)
    (originalCnf -> reducedCnf)
    step

theorem ay_pplc_step_forward
    (originalCnf : Prop) (reducedCnf : Prop)
    (pureLiterals : Prop) (polarityWitness : Prop) :
    AyPureLiteralStep
      originalCnf reducedCnf pureLiterals polarityWitness ->
    originalCnf ->
    reducedCnf := by
  intro step
  exact ay_pplc_conj_right
    (AyPurityCertificate pureLiterals polarityWitness)
    (originalCnf -> reducedCnf)
    step

theorem ay_pplc_report_step
    (originalCnf : Prop) (reducedCnf : Prop)
    (pureLiterals : Prop) (polarityWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedPureLiteralReport
      originalCnf reducedCnf pureLiterals polarityWitness
      reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyPureLiteralStep originalCnf reducedCnf pureLiterals polarityWitness := by
  intro accepted
  exact ay_pplc_conj_left
    (AyPureLiteralStep originalCnf reducedCnf pureLiterals polarityWitness)
    (AyConj
      (AyAssignmentExtension
        reducedCnf originalCnf reducedModel extendedModel)
      (AyConj
        (AyReconstructionChain originalCnf reducedCnf)
        (AyCacheEvidence
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest)))
    accepted

theorem ay_pplc_report_extension
    (originalCnf : Prop) (reducedCnf : Prop)
    (pureLiterals : Prop) (polarityWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedPureLiteralReport
      originalCnf reducedCnf pureLiterals polarityWitness
      reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyAssignmentExtension reducedCnf originalCnf reducedModel extendedModel := by
  intro accepted
  exact ay_pplc_conj_left
    (AyAssignmentExtension reducedCnf originalCnf reducedModel extendedModel)
    (AyConj
      (AyReconstructionChain originalCnf reducedCnf)
      (AyCacheEvidence
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))
    (ay_pplc_conj_right
      (AyPureLiteralStep originalCnf reducedCnf pureLiterals polarityWitness)
      (AyConj
        (AyAssignmentExtension
          reducedCnf originalCnf reducedModel extendedModel)
        (AyConj
          (AyReconstructionChain originalCnf reducedCnf)
          (AyCacheEvidence
            cachedEpoch currentEpoch cachedManifest runManifest
            cachedDigest runDigest)))
      accepted)

theorem ay_pplc_report_chain
    (originalCnf : Prop) (reducedCnf : Prop)
    (pureLiterals : Prop) (polarityWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedPureLiteralReport
      originalCnf reducedCnf pureLiterals polarityWitness
      reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyReconstructionChain originalCnf reducedCnf := by
  intro accepted
  exact ay_pplc_conj_left
    (AyReconstructionChain originalCnf reducedCnf)
    (AyCacheEvidence
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pplc_conj_right
      (AyAssignmentExtension reducedCnf originalCnf reducedModel extendedModel)
      (AyConj
        (AyReconstructionChain originalCnf reducedCnf)
        (AyCacheEvidence
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      (ay_pplc_conj_right
        (AyPureLiteralStep
          originalCnf reducedCnf pureLiterals polarityWitness)
        (AyConj
          (AyAssignmentExtension
            reducedCnf originalCnf reducedModel extendedModel)
          (AyConj
            (AyReconstructionChain originalCnf reducedCnf)
            (AyCacheEvidence
              cachedEpoch currentEpoch cachedManifest runManifest
              cachedDigest runDigest)))
        accepted))

theorem ay_pplc_log_report
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (pureLiterals : Prop) (polarityWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedPureLiteralLogEntry
      previousLog nextLog originalCnf reducedCnf pureLiterals
      polarityWitness reducedModel extendedModel cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AyAcceptedPureLiteralReport
      originalCnf reducedCnf pureLiterals polarityWitness
      reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest := by
  intro entry
  exact ay_pplc_conj_left
    (AyAcceptedPureLiteralReport
      originalCnf reducedCnf pureLiterals polarityWitness
      reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest)
    nextLog
    (ay_pplc_conj_right previousLog
      (AyConj
        (AyAcceptedPureLiteralReport
          originalCnf reducedCnf pureLiterals polarityWitness
          reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
          runManifest cachedDigest runDigest)
        nextLog)
      entry)

theorem ay_pplc_extend_sat
    (originalCnf : Prop) (reducedCnf : Prop)
    (pureLiterals : Prop) (polarityWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedPureLiteralReport
      originalCnf reducedCnf pureLiterals polarityWitness
      reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AySat reducedCnf reducedModel ->
    AySat originalCnf extendedModel := by
  intro accepted
  exact ay_pplc_report_extension originalCnf reducedCnf pureLiterals
    polarityWitness reducedModel extendedModel cachedEpoch currentEpoch
    cachedManifest runManifest cachedDigest runDigest accepted

theorem ay_pplc_unsat_transport
    (originalCnf : Prop) (reducedCnf : Prop)
    (pureLiterals : Prop) (polarityWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedPureLiteralReport
      originalCnf reducedCnf pureLiterals polarityWitness
      reducedModel extendedModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyReplay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay hcertificate horiginal
  exact replay
    (ay_pplc_equisat_forward originalCnf reducedCnf
      (ay_pplc_report_chain originalCnf reducedCnf pureLiterals
        polarityWitness reducedModel extendedModel cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest accepted)
      horiginal)
    hcertificate

theorem ay_pplc_public_sat
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (pureLiterals : Prop) (polarityWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedPureLiteralLogEntry
      previousLog nextLog originalCnf reducedCnf pureLiterals
      polarityWitness reducedModel extendedModel cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AySat reducedCnf reducedModel ->
    exitCode ->
    AyPublicResult originalCnf extendedModel certificate conflict exitCode := by
  intro entry sat hexit
  exact ay_pplc_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf extendedModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pplc_conj_intro exitCode (AySat originalCnf extendedModel)
      hexit
      (ay_pplc_extend_sat originalCnf reducedCnf pureLiterals
        polarityWitness reducedModel extendedModel cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest
        (ay_pplc_log_report previousLog nextLog originalCnf reducedCnf
          pureLiterals polarityWitness reducedModel extendedModel cachedEpoch
          currentEpoch cachedManifest runManifest cachedDigest runDigest entry)
        sat))

theorem ay_pplc_public_unsat
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (pureLiterals : Prop) (polarityWitness : Prop)
    (reducedModel : Prop) (extendedModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedPureLiteralLogEntry
      previousLog nextLog originalCnf reducedCnf pureLiterals
      polarityWitness reducedModel extendedModel cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AyReplay reducedCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf extendedModel certificate conflict exitCode := by
  intro entry replay hexit
  exact ay_pplc_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf extendedModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pplc_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      (ay_pplc_unsat_transport originalCnf reducedCnf pureLiterals
        polarityWitness reducedModel extendedModel cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest certificate conflict
        (ay_pplc_log_report previousLog nextLog originalCnf reducedCnf
          pureLiterals polarityWitness reducedModel extendedModel cachedEpoch
          currentEpoch cachedManifest runManifest cachedDigest runDigest entry)
        replay))

theorem ay_pplc_failure_missing
    (missingPurity : Prop) (stalePurity : Prop)
    (badPolarity : Prop) (cacheMismatch : Prop) :
    missingPurity ->
    AyPureLiteralFailure
      missingPurity stalePurity badPolarity cacheMismatch := by
  intro hmissing
  exact ay_pplc_disj_left missingPurity
    (AyDisj stalePurity (AyDisj badPolarity cacheMismatch))
    hmissing

theorem ay_pplc_failure_stale
    (missingPurity : Prop) (stalePurity : Prop)
    (badPolarity : Prop) (cacheMismatch : Prop) :
    stalePurity ->
    AyPureLiteralFailure
      missingPurity stalePurity badPolarity cacheMismatch := by
  intro hstale
  exact ay_pplc_disj_right missingPurity
    (AyDisj stalePurity (AyDisj badPolarity cacheMismatch))
    (ay_pplc_disj_left stalePurity
      (AyDisj badPolarity cacheMismatch)
      hstale)

theorem ay_pplc_failure_bad_polarity
    (missingPurity : Prop) (stalePurity : Prop)
    (badPolarity : Prop) (cacheMismatch : Prop) :
    badPolarity ->
    AyPureLiteralFailure
      missingPurity stalePurity badPolarity cacheMismatch := by
  intro hbad
  exact ay_pplc_disj_right missingPurity
    (AyDisj stalePurity (AyDisj badPolarity cacheMismatch))
    (ay_pplc_disj_right stalePurity
      (AyDisj badPolarity cacheMismatch)
      (ay_pplc_disj_left badPolarity cacheMismatch hbad))

theorem ay_pplc_failure_cache_mismatch
    (missingPurity : Prop) (stalePurity : Prop)
    (badPolarity : Prop) (cacheMismatch : Prop) :
    cacheMismatch ->
    AyPureLiteralFailure
      missingPurity stalePurity badPolarity cacheMismatch := by
  intro hcache
  exact ay_pplc_disj_right missingPurity
    (AyDisj stalePurity (AyDisj badPolarity cacheMismatch))
    (ay_pplc_disj_right stalePurity
      (AyDisj badPolarity cacheMismatch)
      (ay_pplc_disj_right badPolarity cacheMismatch hcache))

theorem ay_pplc_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingPurity : Prop) (stalePurity : Prop)
    (badPolarity : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticPureLiteralLogEntry
      previousLog nextLog currentCnf missingPurity stalePurity
      badPolarity cacheMismatch recompute diagnostic ->
    AyPureLiteralFailure
      missingPurity stalePurity badPolarity cacheMismatch := by
  intro entry
  exact ay_pplc_conj_left
    (AyPureLiteralFailure missingPurity stalePurity badPolarity cacheMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pplc_conj_left
      (AyConj
        (AyPureLiteralFailure
          missingPurity stalePurity badPolarity cacheMismatch)
        (AyConj
          (AyRecomputeObligation currentCnf recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_pplc_conj_right previousLog
        (AyConj
          (AyConj
            (AyPureLiteralFailure
              missingPurity stalePurity badPolarity cacheMismatch)
            (AyConj
              (AyRecomputeObligation currentCnf recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_pplc_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingPurity : Prop) (stalePurity : Prop)
    (badPolarity : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticPureLiteralLogEntry
      previousLog nextLog currentCnf missingPurity stalePurity
      badPolarity cacheMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_pplc_conj_right
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pplc_conj_right
      (AyPureLiteralFailure missingPurity stalePurity badPolarity cacheMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pplc_conj_left
        (AyConj
          (AyPureLiteralFailure
            missingPurity stalePurity badPolarity cacheMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pplc_conj_right previousLog
          (AyConj
            (AyConj
              (AyPureLiteralFailure
                missingPurity stalePurity badPolarity cacheMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pplc_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingPurity : Prop) (stalePurity : Prop)
    (badPolarity : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticPureLiteralLogEntry
      previousLog nextLog currentCnf missingPurity stalePurity
      badPolarity cacheMismatch recompute diagnostic ->
    AyRecomputeObligation currentCnf recompute := by
  intro entry
  exact ay_pplc_conj_left
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pplc_conj_right
      (AyPureLiteralFailure missingPurity stalePurity badPolarity cacheMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pplc_conj_left
        (AyConj
          (AyPureLiteralFailure
            missingPurity stalePurity badPolarity cacheMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pplc_conj_right previousLog
          (AyConj
            (AyConj
              (AyPureLiteralFailure
                missingPurity stalePurity badPolarity cacheMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pplc_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingPurity : Prop) (stalePurity : Prop)
    (badPolarity : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticPureLiteralLogEntry
      previousLog nextLog currentCnf missingPurity stalePurity
      badPolarity cacheMismatch recompute diagnostic ->
    AyConj
      (AyPureLiteralFailure missingPurity stalePurity badPolarity cacheMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_pplc_conj_intro
    (AyPureLiteralFailure missingPurity stalePurity badPolarity cacheMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pplc_diagnostic_failure previousLog nextLog currentCnf
      missingPurity stalePurity badPolarity cacheMismatch recompute
      diagnostic entry)
    (ay_pplc_conj_intro
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pplc_diagnostic_recompute previousLog nextLog currentCnf
        missingPurity stalePurity badPolarity cacheMismatch recompute
        diagnostic entry)
      (ay_pplc_diagnostic_no_claim previousLog nextLog currentCnf
        missingPurity stalePurity badPolarity cacheMismatch recompute
        diagnostic entry))
