-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Blocked-clause elimination certificate soundness. The propositions stand
-- for blocking-literal certificates for removed clauses, reconstruction and
-- equisatisfiability chains, cache/digest agreement, diagnostics, and public
-- SAT/UNSAT outcomes.

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

def AyBlockingLiteralCertificate
    (removedClauses : Prop) (blockingLiterals : Prop) :=
  AyConj removedClauses blockingLiterals

def AyBlockedClauseCertificate
    (originalCnf : Prop) (reducedCnf : Prop)
    (removedClauses : Prop) (blockingLiterals : Prop) :=
  AyConj
    (AyBlockingLiteralCertificate removedClauses blockingLiterals)
    (originalCnf -> reducedCnf)

def AyReconstructionMap
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  AyConj
    (AySat reducedCnf reducedModel -> AySat originalCnf originalModel)
    (AyEquisat originalCnf reducedCnf)

def AyCacheEvidence
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyIdMatch cachedEpoch currentEpoch)
    (AyConj
      (AyIdMatch cachedManifest runManifest)
      (AyDigestMatch cachedDigest runDigest))

def AyAcceptedBceReport
    (originalCnf : Prop) (reducedCnf : Prop)
    (removedClauses : Prop) (blockingLiterals : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyConj
    (AyBlockedClauseCertificate
      originalCnf reducedCnf removedClauses blockingLiterals)
    (AyConj
      (AyReconstructionMap reducedCnf originalCnf reducedModel originalModel)
      (AyCacheEvidence
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))

def AyBceCertificateFailure
    (missingCertificate : Prop) (staleCertificate : Prop)
    (badBlockingLiteral : Prop) (cacheMismatch : Prop) :=
  AyDisj missingCertificate
    (AyDisj staleCertificate (AyDisj badBlockingLiteral cacheMismatch))

def AyNoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def AyRecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  AyConj currentCnf recompute

def AyAppendOnlyEntry (previousLog : Prop) (entry : Prop) (nextLog : Prop) :=
  AyConj previousLog (AyConj entry nextLog)

def AyAcceptedBceLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (removedClauses : Prop) (blockingLiterals : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyAcceptedBceReport
      originalCnf reducedCnf removedClauses blockingLiterals
      reducedModel originalModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest)
    nextLog

def AyDiagnosticBceLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingCertificate : Prop) (staleCertificate : Prop)
    (badBlockingLiteral : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  AyAppendOnlyEntry previousLog
    (AyConj
      (AyBceCertificateFailure
        missingCertificate staleCertificate badBlockingLiteral cacheMismatch)
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

theorem ay_pbcc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyConj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pbcc_conj_left
    (left : Prop) (right : Prop) :
    AyConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pbcc_conj_right
    (left : Prop) (right : Prop) :
    AyConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pbcc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyDisj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pbcc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyDisj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pbcc_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pbcc_conj_left (before -> after) (after -> before) eq

theorem ay_pbcc_blocking_removed
    (removedClauses : Prop) (blockingLiterals : Prop) :
    AyBlockingLiteralCertificate removedClauses blockingLiterals ->
    removedClauses := by
  intro cert
  exact ay_pbcc_conj_left removedClauses blockingLiterals cert

theorem ay_pbcc_blocking_literals
    (removedClauses : Prop) (blockingLiterals : Prop) :
    AyBlockingLiteralCertificate removedClauses blockingLiterals ->
    blockingLiterals := by
  intro cert
  exact ay_pbcc_conj_right removedClauses blockingLiterals cert

theorem ay_pbcc_certificate_blocking
    (originalCnf : Prop) (reducedCnf : Prop)
    (removedClauses : Prop) (blockingLiterals : Prop) :
    AyBlockedClauseCertificate
      originalCnf reducedCnf removedClauses blockingLiterals ->
    AyBlockingLiteralCertificate removedClauses blockingLiterals := by
  intro cert
  exact ay_pbcc_conj_left
    (AyBlockingLiteralCertificate removedClauses blockingLiterals)
    (originalCnf -> reducedCnf)
    cert

theorem ay_pbcc_certificate_forward
    (originalCnf : Prop) (reducedCnf : Prop)
    (removedClauses : Prop) (blockingLiterals : Prop) :
    AyBlockedClauseCertificate
      originalCnf reducedCnf removedClauses blockingLiterals ->
    originalCnf ->
    reducedCnf := by
  intro cert
  exact ay_pbcc_conj_right
    (AyBlockingLiteralCertificate removedClauses blockingLiterals)
    (originalCnf -> reducedCnf)
    cert

theorem ay_pbcc_report_certificate
    (originalCnf : Prop) (reducedCnf : Prop)
    (removedClauses : Prop) (blockingLiterals : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedBceReport
      originalCnf reducedCnf removedClauses blockingLiterals
      reducedModel originalModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyBlockedClauseCertificate
      originalCnf reducedCnf removedClauses blockingLiterals := by
  intro accepted
  exact ay_pbcc_conj_left
    (AyBlockedClauseCertificate
      originalCnf reducedCnf removedClauses blockingLiterals)
    (AyConj
      (AyReconstructionMap reducedCnf originalCnf reducedModel originalModel)
      (AyCacheEvidence
        cachedEpoch currentEpoch cachedManifest runManifest
        cachedDigest runDigest))
    accepted

theorem ay_pbcc_report_reconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (removedClauses : Prop) (blockingLiterals : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedBceReport
      originalCnf reducedCnf removedClauses blockingLiterals
      reducedModel originalModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyReconstructionMap reducedCnf originalCnf reducedModel originalModel := by
  intro accepted
  exact ay_pbcc_conj_left
    (AyReconstructionMap reducedCnf originalCnf reducedModel originalModel)
    (AyCacheEvidence
      cachedEpoch currentEpoch cachedManifest runManifest
      cachedDigest runDigest)
    (ay_pbcc_conj_right
      (AyBlockedClauseCertificate
        originalCnf reducedCnf removedClauses blockingLiterals)
      (AyConj
        (AyReconstructionMap reducedCnf originalCnf reducedModel originalModel)
        (AyCacheEvidence
          cachedEpoch currentEpoch cachedManifest runManifest
          cachedDigest runDigest))
      accepted)

theorem ay_pbcc_reconstruction_sat
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    AyReconstructionMap reducedCnf originalCnf reducedModel originalModel ->
    AySat reducedCnf reducedModel ->
    AySat originalCnf originalModel := by
  intro reconstruction
  exact ay_pbcc_conj_left
    (AySat reducedCnf reducedModel -> AySat originalCnf originalModel)
    (AyEquisat originalCnf reducedCnf)
    reconstruction

theorem ay_pbcc_reconstruction_equisat
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :
    AyReconstructionMap reducedCnf originalCnf reducedModel originalModel ->
    AyEquisat originalCnf reducedCnf := by
  intro reconstruction
  exact ay_pbcc_conj_right
    (AySat reducedCnf reducedModel -> AySat originalCnf originalModel)
    (AyEquisat originalCnf reducedCnf)
    reconstruction

theorem ay_pbcc_log_report
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (removedClauses : Prop) (blockingLiterals : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedBceLogEntry
      previousLog nextLog originalCnf reducedCnf removedClauses
      blockingLiterals reducedModel originalModel cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AyAcceptedBceReport
      originalCnf reducedCnf removedClauses blockingLiterals
      reducedModel originalModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest := by
  intro entry
  exact ay_pbcc_conj_left
    (AyAcceptedBceReport
      originalCnf reducedCnf removedClauses blockingLiterals
      reducedModel originalModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest)
    nextLog
    (ay_pbcc_conj_right previousLog
      (AyConj
        (AyAcceptedBceReport
          originalCnf reducedCnf removedClauses blockingLiterals
          reducedModel originalModel cachedEpoch currentEpoch cachedManifest
          runManifest cachedDigest runDigest)
        nextLog)
      entry)

theorem ay_pbcc_sat_transport
    (originalCnf : Prop) (reducedCnf : Prop)
    (removedClauses : Prop) (blockingLiterals : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop) :
    AyAcceptedBceReport
      originalCnf reducedCnf removedClauses blockingLiterals
      reducedModel originalModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AySat reducedCnf reducedModel ->
    AySat originalCnf originalModel := by
  intro accepted
  exact ay_pbcc_reconstruction_sat reducedCnf originalCnf
    reducedModel originalModel
    (ay_pbcc_report_reconstruction originalCnf reducedCnf removedClauses
      blockingLiterals reducedModel originalModel cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest accepted)

theorem ay_pbcc_unsat_transport
    (originalCnf : Prop) (reducedCnf : Prop)
    (removedClauses : Prop) (blockingLiterals : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) :
    AyAcceptedBceReport
      originalCnf reducedCnf removedClauses blockingLiterals
      reducedModel originalModel cachedEpoch currentEpoch cachedManifest
      runManifest cachedDigest runDigest ->
    AyReplay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay hcertificate horiginal
  exact replay
    (ay_pbcc_equisat_forward originalCnf reducedCnf
      (ay_pbcc_reconstruction_equisat reducedCnf originalCnf
        reducedModel originalModel
        (ay_pbcc_report_reconstruction originalCnf reducedCnf
          removedClauses blockingLiterals reducedModel originalModel
          cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
          runDigest accepted))
      horiginal)
    hcertificate

theorem ay_pbcc_public_sat
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (removedClauses : Prop) (blockingLiterals : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedBceLogEntry
      previousLog nextLog originalCnf reducedCnf removedClauses
      blockingLiterals reducedModel originalModel cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AySat reducedCnf reducedModel ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry sat hexit
  exact ay_pbcc_disj_left
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pbcc_conj_intro exitCode (AySat originalCnf originalModel)
      hexit
      (ay_pbcc_sat_transport originalCnf reducedCnf removedClauses
        blockingLiterals reducedModel originalModel cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest
        (ay_pbcc_log_report previousLog nextLog originalCnf reducedCnf
          removedClauses blockingLiterals reducedModel originalModel
          cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
          runDigest entry)
        sat))

theorem ay_pbcc_public_unsat
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (removedClauses : Prop) (blockingLiterals : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (cachedEpoch : Prop) (currentEpoch : Prop)
    (cachedManifest : Prop) (runManifest : Prop)
    (cachedDigest : Prop) (runDigest : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    AyAcceptedBceLogEntry
      previousLog nextLog originalCnf reducedCnf removedClauses
      blockingLiterals reducedModel originalModel cachedEpoch currentEpoch
      cachedManifest runManifest cachedDigest runDigest ->
    AyReplay reducedCnf certificate conflict ->
    exitCode ->
    AyPublicResult originalCnf originalModel certificate conflict exitCode := by
  intro entry replay hexit
  exact ay_pbcc_disj_right
    (AyExitCodeSound exitCode (AySat originalCnf originalModel))
    (AyExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pbcc_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      hexit
      (ay_pbcc_unsat_transport originalCnf reducedCnf removedClauses
        blockingLiterals reducedModel originalModel cachedEpoch currentEpoch
        cachedManifest runManifest cachedDigest runDigest certificate conflict
        (ay_pbcc_log_report previousLog nextLog originalCnf reducedCnf
          removedClauses blockingLiterals reducedModel originalModel
          cachedEpoch currentEpoch cachedManifest runManifest cachedDigest
          runDigest entry)
        replay))

theorem ay_pbcc_failure_missing
    (missingCertificate : Prop) (staleCertificate : Prop)
    (badBlockingLiteral : Prop) (cacheMismatch : Prop) :
    missingCertificate ->
    AyBceCertificateFailure
      missingCertificate staleCertificate badBlockingLiteral cacheMismatch := by
  intro hmissing
  exact ay_pbcc_disj_left missingCertificate
    (AyDisj staleCertificate (AyDisj badBlockingLiteral cacheMismatch))
    hmissing

theorem ay_pbcc_failure_stale
    (missingCertificate : Prop) (staleCertificate : Prop)
    (badBlockingLiteral : Prop) (cacheMismatch : Prop) :
    staleCertificate ->
    AyBceCertificateFailure
      missingCertificate staleCertificate badBlockingLiteral cacheMismatch := by
  intro hstale
  exact ay_pbcc_disj_right missingCertificate
    (AyDisj staleCertificate (AyDisj badBlockingLiteral cacheMismatch))
    (ay_pbcc_disj_left staleCertificate
      (AyDisj badBlockingLiteral cacheMismatch)
      hstale)

theorem ay_pbcc_failure_bad_blocking_literal
    (missingCertificate : Prop) (staleCertificate : Prop)
    (badBlockingLiteral : Prop) (cacheMismatch : Prop) :
    badBlockingLiteral ->
    AyBceCertificateFailure
      missingCertificate staleCertificate badBlockingLiteral cacheMismatch := by
  intro hbad
  exact ay_pbcc_disj_right missingCertificate
    (AyDisj staleCertificate (AyDisj badBlockingLiteral cacheMismatch))
    (ay_pbcc_disj_right staleCertificate
      (AyDisj badBlockingLiteral cacheMismatch)
      (ay_pbcc_disj_left badBlockingLiteral cacheMismatch hbad))

theorem ay_pbcc_failure_cache_mismatch
    (missingCertificate : Prop) (staleCertificate : Prop)
    (badBlockingLiteral : Prop) (cacheMismatch : Prop) :
    cacheMismatch ->
    AyBceCertificateFailure
      missingCertificate staleCertificate badBlockingLiteral cacheMismatch := by
  intro hcache
  exact ay_pbcc_disj_right missingCertificate
    (AyDisj staleCertificate (AyDisj badBlockingLiteral cacheMismatch))
    (ay_pbcc_disj_right staleCertificate
      (AyDisj badBlockingLiteral cacheMismatch)
      (ay_pbcc_disj_right badBlockingLiteral cacheMismatch hcache))

theorem ay_pbcc_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingCertificate : Prop) (staleCertificate : Prop)
    (badBlockingLiteral : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticBceLogEntry
      previousLog nextLog currentCnf missingCertificate staleCertificate
      badBlockingLiteral cacheMismatch recompute diagnostic ->
    AyBceCertificateFailure
      missingCertificate staleCertificate badBlockingLiteral cacheMismatch := by
  intro entry
  exact ay_pbcc_conj_left
    (AyBceCertificateFailure
      missingCertificate staleCertificate badBlockingLiteral cacheMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pbcc_conj_left
      (AyConj
        (AyBceCertificateFailure
          missingCertificate staleCertificate badBlockingLiteral cacheMismatch)
        (AyConj
          (AyRecomputeObligation currentCnf recompute)
          (AyNoSemanticClaim diagnostic)))
      nextLog
      (ay_pbcc_conj_right previousLog
        (AyConj
          (AyConj
            (AyBceCertificateFailure
              missingCertificate staleCertificate badBlockingLiteral
              cacheMismatch)
            (AyConj
              (AyRecomputeObligation currentCnf recompute)
              (AyNoSemanticClaim diagnostic)))
          nextLog)
        entry))

theorem ay_pbcc_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingCertificate : Prop) (staleCertificate : Prop)
    (badBlockingLiteral : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticBceLogEntry
      previousLog nextLog currentCnf missingCertificate staleCertificate
      badBlockingLiteral cacheMismatch recompute diagnostic ->
    AyNoSemanticClaim diagnostic := by
  intro entry
  exact ay_pbcc_conj_right
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pbcc_conj_right
      (AyBceCertificateFailure
        missingCertificate staleCertificate badBlockingLiteral cacheMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pbcc_conj_left
        (AyConj
          (AyBceCertificateFailure
            missingCertificate staleCertificate badBlockingLiteral cacheMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pbcc_conj_right previousLog
          (AyConj
            (AyConj
              (AyBceCertificateFailure
                missingCertificate staleCertificate badBlockingLiteral
                cacheMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pbcc_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingCertificate : Prop) (staleCertificate : Prop)
    (badBlockingLiteral : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticBceLogEntry
      previousLog nextLog currentCnf missingCertificate staleCertificate
      badBlockingLiteral cacheMismatch recompute diagnostic ->
    AyRecomputeObligation currentCnf recompute := by
  intro entry
  exact ay_pbcc_conj_left
    (AyRecomputeObligation currentCnf recompute)
    (AyNoSemanticClaim diagnostic)
    (ay_pbcc_conj_right
      (AyBceCertificateFailure
        missingCertificate staleCertificate badBlockingLiteral cacheMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic))
      (ay_pbcc_conj_left
        (AyConj
          (AyBceCertificateFailure
            missingCertificate staleCertificate badBlockingLiteral cacheMismatch)
          (AyConj
            (AyRecomputeObligation currentCnf recompute)
            (AyNoSemanticClaim diagnostic)))
        nextLog
        (ay_pbcc_conj_right previousLog
          (AyConj
            (AyConj
              (AyBceCertificateFailure
                missingCertificate staleCertificate badBlockingLiteral
                cacheMismatch)
              (AyConj
                (AyRecomputeObligation currentCnf recompute)
                (AyNoSemanticClaim diagnostic)))
            nextLog)
          entry)))

theorem ay_pbcc_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingCertificate : Prop) (staleCertificate : Prop)
    (badBlockingLiteral : Prop) (cacheMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    AyDiagnosticBceLogEntry
      previousLog nextLog currentCnf missingCertificate staleCertificate
      badBlockingLiteral cacheMismatch recompute diagnostic ->
    AyConj
      (AyBceCertificateFailure
        missingCertificate staleCertificate badBlockingLiteral cacheMismatch)
      (AyConj
        (AyRecomputeObligation currentCnf recompute)
        (AyNoSemanticClaim diagnostic)) := by
  intro entry
  exact ay_pbcc_conj_intro
    (AyBceCertificateFailure
      missingCertificate staleCertificate badBlockingLiteral cacheMismatch)
    (AyConj
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic))
    (ay_pbcc_diagnostic_failure previousLog nextLog currentCnf
      missingCertificate staleCertificate badBlockingLiteral cacheMismatch
      recompute diagnostic entry)
    (ay_pbcc_conj_intro
      (AyRecomputeObligation currentCnf recompute)
      (AyNoSemanticClaim diagnostic)
      (ay_pbcc_diagnostic_recompute previousLog nextLog currentCnf
        missingCertificate staleCertificate badBlockingLiteral cacheMismatch
        recompute diagnostic entry)
      (ay_pbcc_diagnostic_no_claim previousLog nextLog currentCnf
        missingCertificate staleCertificate badBlockingLiteral cacheMismatch
        recompute diagnostic entry))
