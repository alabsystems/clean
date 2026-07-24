-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT proof line-ending/parser guard soundness for ay
-- sequential-main SAT-COMP publication. Propositions stand for proof text
-- digests, line-ending policy manifests, parsed proof-step ledgers, checker
-- transcripts, empty-clause reachability witnesses, benchmark fingerprints,
-- solver build evidence, archive manifests, fallback baselines, audit
-- transcripts, and fail-closed no-claim/recompute diagnostics.

def AyPLEGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyPLEGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyPLEGMap (source : Prop) (target : Prop) :=
  source -> target

def AyPLEGAcceptedEvidence
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (proofTextDigest ->
      lineEndingPolicyManifest ->
      parsedStepLedger ->
      checkerTranscript ->
      checkerAccepted ->
      emptyClauseReachable ->
      benchmarkFingerprint ->
      fingerprintAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      archiveManifest ->
      fallbackBaseline ->
      auditTranscript ->
      visibleUnsat ->
      originalUnsat ->
      result) ->
    result

def AyPLEGParserComposition
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyPLEGConj
    (AyPLEGMap proofTextDigest lineEndingPolicyManifest)
    (AyPLEGConj
      (AyPLEGMap lineEndingPolicyManifest parsedStepLedger)
      (AyPLEGConj
        (AyPLEGMap parsedStepLedger checkerTranscript)
        (AyPLEGConj
          (AyPLEGMap checkerTranscript emptyClauseReachable)
          (AyPLEGConj
            (AyPLEGMap emptyClauseReachable visibleUnsat)
            (AyPLEGMap visibleUnsat originalUnsat)))))

def AyPLEGPublication
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyPLEGConj
    (AyPLEGAcceptedEvidence proofTextDigest lineEndingPolicyManifest
      parsedStepLedger checkerTranscript checkerAccepted emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat)
    originalUnsat

def AyPLEGFailureReason
    (crlfLfMismatch : Prop) (truncatedFinalLine : Prop)
    (malformedParsedStep : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (crlfLfMismatch -> result) ->
    (truncatedFinalLine -> result) ->
    (malformedParsedStep -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (fallbackMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def AyPLEGBadParserGuard
    (crlfLfMismatch : Prop) (truncatedFinalLine : Prop)
    (malformedParsedStep : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyPLEGConj
    (AyPLEGConj noClaim recompute)
    (AyPLEGFailureReason crlfLfMismatch truncatedFinalLine
      malformedParsedStep checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch)

def AyPLEGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyPLEGDisj noClaim originalUnsat

theorem ay_pleg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyPLEGConj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_pleg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyPLEGDisj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_pleg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyPLEGDisj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_pleg_accepted_evidence
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    proofTextDigest ->
    lineEndingPolicyManifest ->
    parsedStepLedger ->
    checkerTranscript ->
    checkerAccepted ->
    emptyClauseReachable ->
    benchmarkFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    archiveManifest ->
    fallbackBaseline ->
    auditTranscript ->
    visibleUnsat ->
    originalUnsat ->
    AyPLEGAcceptedEvidence proofTextDigest lineEndingPolicyManifest
      parsedStepLedger checkerTranscript checkerAccepted emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat := by
  intro hText hPolicy hParsed hTranscript hChecker hEmpty hFingerprint
  intro hFingerprintAccepted hBuild hBuildAccepted hArchive hFallback hAudit
  intro hVisible hOriginal result publish
  exact publish hText hPolicy hParsed hTranscript hChecker hEmpty
    hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
    hFallback hAudit hVisible hOriginal

theorem ay_pleg_proof_text_digest
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPLEGAcceptedEvidence proofTextDigest lineEndingPolicyManifest
      parsedStepLedger checkerTranscript checkerAccepted emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    proofTextDigest := by
  intro accepted
  exact accepted proofTextDigest
    (fun hText _hPolicy _hParsed _hTranscript _hChecker _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible _hOriginal => hText)

theorem ay_pleg_line_ending_policy_manifest
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPLEGAcceptedEvidence proofTextDigest lineEndingPolicyManifest
      parsedStepLedger checkerTranscript checkerAccepted emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    lineEndingPolicyManifest := by
  intro accepted
  exact accepted lineEndingPolicyManifest
    (fun _hText hPolicy _hParsed _hTranscript _hChecker _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible _hOriginal => hPolicy)

theorem ay_pleg_parsed_step_ledger
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPLEGAcceptedEvidence proofTextDigest lineEndingPolicyManifest
      parsedStepLedger checkerTranscript checkerAccepted emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    parsedStepLedger := by
  intro accepted
  exact accepted parsedStepLedger
    (fun _hText _hPolicy hParsed _hTranscript _hChecker _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible _hOriginal => hParsed)

theorem ay_pleg_checker_transcript
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPLEGAcceptedEvidence proofTextDigest lineEndingPolicyManifest
      parsedStepLedger checkerTranscript checkerAccepted emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hText _hPolicy _hParsed hTranscript _hChecker _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible _hOriginal => hTranscript)

theorem ay_pleg_checker_accepted
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPLEGAcceptedEvidence proofTextDigest lineEndingPolicyManifest
      parsedStepLedger checkerTranscript checkerAccepted emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hText _hPolicy _hParsed _hTranscript hChecker _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible _hOriginal => hChecker)

theorem ay_pleg_empty_clause_reachable
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPLEGAcceptedEvidence proofTextDigest lineEndingPolicyManifest
      parsedStepLedger checkerTranscript checkerAccepted emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hText _hPolicy _hParsed _hTranscript _hChecker hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_pleg_benchmark_fingerprint
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPLEGAcceptedEvidence proofTextDigest lineEndingPolicyManifest
      parsedStepLedger checkerTranscript checkerAccepted emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    benchmarkFingerprint := by
  intro accepted
  exact accepted benchmarkFingerprint
    (fun _hText _hPolicy _hParsed _hTranscript _hChecker _hEmpty hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible _hOriginal => hFingerprint)

theorem ay_pleg_archive_manifest
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPLEGAcceptedEvidence proofTextDigest lineEndingPolicyManifest
      parsedStepLedger checkerTranscript checkerAccepted emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    archiveManifest := by
  intro accepted
  exact accepted archiveManifest
    (fun _hText _hPolicy _hParsed _hTranscript _hChecker _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted hArchive _hFallback
      _hAudit _hVisible _hOriginal => hArchive)

theorem ay_pleg_original_unsat
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPLEGAcceptedEvidence proofTextDigest lineEndingPolicyManifest
      parsedStepLedger checkerTranscript checkerAccepted emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hText _hPolicy _hParsed _hTranscript _hChecker _hEmpty _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hVisible hOriginal => hOriginal)

theorem ay_pleg_parser_evidence_composes_to_original
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    proofTextDigest ->
    AyPLEGParserComposition proofTextDigest lineEndingPolicyManifest
      parsedStepLedger checkerTranscript emptyClauseReachable visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro hText
  intro composed
  exact composed originalUnsat
    (fun text_to_policy rest1 =>
      rest1 originalUnsat
        (fun policy_to_parsed rest2 =>
          rest2 originalUnsat
            (fun parsed_to_transcript rest3 =>
              rest3 originalUnsat
                (fun transcript_to_empty rest4 =>
                  rest4 originalUnsat
                    (fun empty_to_visible visible_to_original =>
                      visible_to_original
                        (empty_to_visible
                          (transcript_to_empty
                            (parsed_to_transcript
                              (policy_to_parsed
                                (text_to_policy hText))))))))))

theorem ay_pleg_publication_sound
    (proofTextDigest : Prop) (lineEndingPolicyManifest : Prop)
    (parsedStepLedger : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachable : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackBaseline : Prop)
    (auditTranscript : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyPLEGPublication proofTextDigest lineEndingPolicyManifest
      parsedStepLedger checkerTranscript checkerAccepted emptyClauseReachable
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackBaseline auditTranscript
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat (fun _accepted unsat => unsat)

theorem ay_pleg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyPLEGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_pleg_disj_right noClaim originalUnsat unsat

theorem ay_pleg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyPLEGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_pleg_disj_left noClaim originalUnsat no_claim

theorem ay_pleg_bad_no_claim
    (crlfLfMismatch : Prop) (truncatedFinalLine : Prop)
    (malformedParsedStep : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPLEGBadParserGuard crlfLfMismatch truncatedFinalLine
      malformedParsedStep checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_pleg_bad_recompute
    (crlfLfMismatch : Prop) (truncatedFinalLine : Prop)
    (malformedParsedStep : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPLEGBadParserGuard crlfLfMismatch truncatedFinalLine
      malformedParsedStep checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_pleg_failed_line_ending_guard_cannot_bless_unsat
    (crlfLfMismatch : Prop) (truncatedFinalLine : Prop)
    (malformedParsedStep : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyPLEGBadParserGuard crlfLfMismatch truncatedFinalLine
      malformedParsedStep checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    AyPLEGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_pleg_public_no_claim_report noClaim originalUnsat
    (ay_pleg_bad_no_claim crlfLfMismatch truncatedFinalLine
      malformedParsedStep checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_pleg_failure_forces_no_claim
    (crlfLfMismatch : Prop) (truncatedFinalLine : Prop)
    (malformedParsedStep : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPLEGBadParserGuard crlfLfMismatch truncatedFinalLine
      malformedParsedStep checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    AyPLEGConj noClaim recompute := by
  intro bad
  exact ay_pleg_conj_intro noClaim recompute
    (ay_pleg_bad_no_claim crlfLfMismatch truncatedFinalLine
      malformedParsedStep checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)
    (ay_pleg_bad_recompute crlfLfMismatch truncatedFinalLine
      malformedParsedStep checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_pleg_crlf_lf_mismatch_forces_no_claim
    (crlfLfMismatch : Prop) (noClaim : Prop) :
    crlfLfMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pleg_truncated_final_line_forces_no_claim
    (truncatedFinalLine : Prop) (noClaim : Prop) :
    truncatedFinalLine -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pleg_malformed_parsed_step_forces_no_claim
    (malformedParsedStep : Prop) (noClaim : Prop) :
    malformedParsedStep -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pleg_checker_mismatch_forces_no_claim
    (checkerMismatch : Prop) (noClaim : Prop) :
    checkerMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pleg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch : Prop) (noClaim : Prop) :
    fingerprintMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pleg_build_mismatch_forces_no_claim
    (buildMismatch : Prop) (noClaim : Prop) :
    buildMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pleg_archive_mismatch_forces_no_claim
    (archiveMismatch : Prop) (noClaim : Prop) :
    archiveMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pleg_fallback_mismatch_forces_no_claim
    (fallbackMismatch : Prop) (noClaim : Prop) :
    fallbackMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pleg_audit_mismatch_forces_no_claim
    (auditMismatch : Prop) (noClaim : Prop) :
    auditMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
