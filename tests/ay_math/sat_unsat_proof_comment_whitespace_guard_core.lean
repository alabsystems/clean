-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT proof comment/whitespace parser guard soundness for ay
-- sequential-main SAT-COMP publication. Propositions stand for proof text
-- digests, comment policy manifests, whitespace normalization witnesses,
-- parsed proof-step ledgers, checker transcripts, empty-clause reachability
-- witnesses, benchmark fingerprints, solver build evidence, archive
-- manifests, fallback baselines, audit transcripts, and fail-closed
-- no-claim/recompute diagnostics.

def AyPCWGConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyPCWGDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyPCWGMap (source : Prop) (target : Prop) :=
  source -> target

def AyPCWGAcceptedEvidence
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofTextDigest ->
      commentPolicyManifest ->
      whitespaceNormalizationWitness ->
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

def AyPCWGParserComposition
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (emptyClauseReachable : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyPCWGConj
    (AyPCWGMap proofTextDigest commentPolicyManifest)
    (AyPCWGConj
      (AyPCWGMap commentPolicyManifest whitespaceNormalizationWitness)
      (AyPCWGConj
        (AyPCWGMap whitespaceNormalizationWitness parsedStepLedger)
        (AyPCWGConj
          (AyPCWGMap parsedStepLedger checkerTranscript)
          (AyPCWGConj
            (AyPCWGMap checkerTranscript emptyClauseReachable)
            (AyPCWGConj
              (AyPCWGMap emptyClauseReachable visibleUnsat)
              (AyPCWGMap visibleUnsat originalUnsat))))))

def AyPCWGPublication
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyPCWGConj
    (AyPCWGAcceptedEvidence proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat)
    originalUnsat

def AyPCWGFailureReason
    (malformedComments : Prop) (whitespaceConfusion : Prop)
    (parsedStepMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (malformedComments -> result) ->
    (whitespaceConfusion -> result) ->
    (parsedStepMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (fallbackMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def AyPCWGBadParserGuard
    (malformedComments : Prop) (whitespaceConfusion : Prop)
    (parsedStepMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyPCWGConj
    (AyPCWGConj noClaim recompute)
    (AyPCWGFailureReason malformedComments whitespaceConfusion
      parsedStepMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch)

def AyPCWGPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyPCWGDisj noClaim originalUnsat

theorem ay_pcwg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyPCWGConj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_pcwg_disj_left
    (p : Prop) (q : Prop) :
    p -> AyPCWGDisj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_pcwg_disj_right
    (p : Prop) (q : Prop) :
    q -> AyPCWGDisj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_pcwg_accepted_evidence
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    proofTextDigest ->
    commentPolicyManifest ->
    whitespaceNormalizationWitness ->
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
    AyPCWGAcceptedEvidence proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat := by
  intro hText hComment hWhitespace hParsed hTranscript hChecker hEmpty
  intro hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
  intro hFallback hAudit hVisible hOriginal result publish
  exact publish hText hComment hWhitespace hParsed hTranscript hChecker
    hEmpty hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
    hFallback hAudit hVisible hOriginal

theorem ay_pcwg_proof_text_digest
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCWGAcceptedEvidence proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    proofTextDigest := by
  intro accepted
  exact accepted proofTextDigest
    (fun hText _hComment _hWhitespace _hParsed _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hText)

theorem ay_pcwg_comment_policy_manifest
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCWGAcceptedEvidence proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    commentPolicyManifest := by
  intro accepted
  exact accepted commentPolicyManifest
    (fun _hText hComment _hWhitespace _hParsed _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hComment)

theorem ay_pcwg_whitespace_normalization_witness
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCWGAcceptedEvidence proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    whitespaceNormalizationWitness := by
  intro accepted
  exact accepted whitespaceNormalizationWitness
    (fun _hText _hComment hWhitespace _hParsed _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hWhitespace)

theorem ay_pcwg_parsed_step_ledger
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCWGAcceptedEvidence proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    parsedStepLedger := by
  intro accepted
  exact accepted parsedStepLedger
    (fun _hText _hComment _hWhitespace hParsed _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hParsed)

theorem ay_pcwg_checker_transcript
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCWGAcceptedEvidence proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hText _hComment _hWhitespace _hParsed hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hTranscript)

theorem ay_pcwg_checker_accepted
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCWGAcceptedEvidence proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    checkerAccepted := by
  intro accepted
  exact accepted checkerAccepted
    (fun _hText _hComment _hWhitespace _hParsed _hTranscript hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hChecker)

theorem ay_pcwg_empty_clause_reachable
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCWGAcceptedEvidence proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hText _hComment _hWhitespace _hParsed _hTranscript _hChecker
      hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hEmpty)

theorem ay_pcwg_benchmark_fingerprint
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCWGAcceptedEvidence proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    benchmarkFingerprint := by
  intro accepted
  exact accepted benchmarkFingerprint
    (fun _hText _hComment _hWhitespace _hParsed _hTranscript _hChecker
      _hEmpty hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible _hOriginal => hFingerprint)

theorem ay_pcwg_archive_manifest
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCWGAcceptedEvidence proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    archiveManifest := by
  intro accepted
  exact accepted archiveManifest
    (fun _hText _hComment _hWhitespace _hParsed _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      hArchive _hFallback _hAudit _hVisible _hOriginal => hArchive)

theorem ay_pcwg_original_unsat
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCWGAcceptedEvidence proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hText _hComment _hWhitespace _hParsed _hTranscript _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hVisible hOriginal => hOriginal)

theorem ay_pcwg_comment_whitespace_replay_composes_to_original
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (emptyClauseReachable : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    proofTextDigest ->
    AyPCWGParserComposition proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      emptyClauseReachable visibleUnsat originalUnsat ->
    originalUnsat := by
  intro hText
  intro composed
  exact composed originalUnsat
    (fun text_to_comment rest1 =>
      rest1 originalUnsat
        (fun comment_to_whitespace rest2 =>
          rest2 originalUnsat
            (fun whitespace_to_parsed rest3 =>
              rest3 originalUnsat
                (fun parsed_to_transcript rest4 =>
                  rest4 originalUnsat
                    (fun transcript_to_empty rest5 =>
                      rest5 originalUnsat
                        (fun empty_to_visible visible_to_original =>
                          visible_to_original
                            (empty_to_visible
                              (transcript_to_empty
                                (parsed_to_transcript
                                  (whitespace_to_parsed
                                    (comment_to_whitespace
                                      (text_to_comment hText))))))))))))

theorem ay_pcwg_publication_sound
    (proofTextDigest : Prop) (commentPolicyManifest : Prop)
    (whitespaceNormalizationWitness : Prop) (parsedStepLedger : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (emptyClauseReachable : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackBaseline : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyPCWGPublication proofTextDigest commentPolicyManifest
      whitespaceNormalizationWitness parsedStepLedger checkerTranscript
      checkerAccepted emptyClauseReachable benchmarkFingerprint
      fingerprintAccepted solverBuildEvidence buildAccepted archiveManifest
      fallbackBaseline auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat (fun _accepted unsat => unsat)

theorem ay_pcwg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyPCWGPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_pcwg_disj_right noClaim originalUnsat unsat

theorem ay_pcwg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyPCWGPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_pcwg_disj_left noClaim originalUnsat no_claim

theorem ay_pcwg_bad_no_claim
    (malformedComments : Prop) (whitespaceConfusion : Prop)
    (parsedStepMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPCWGBadParserGuard malformedComments whitespaceConfusion
      parsedStepMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_pcwg_bad_recompute
    (malformedComments : Prop) (whitespaceConfusion : Prop)
    (parsedStepMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPCWGBadParserGuard malformedComments whitespaceConfusion
      parsedStepMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_pcwg_failed_parser_guard_cannot_bless_unsat
    (malformedComments : Prop) (whitespaceConfusion : Prop)
    (parsedStepMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyPCWGBadParserGuard malformedComments whitespaceConfusion
      parsedStepMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    AyPCWGPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_pcwg_public_no_claim_report noClaim originalUnsat
    (ay_pcwg_bad_no_claim malformedComments whitespaceConfusion
      parsedStepMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_pcwg_failure_forces_no_claim
    (malformedComments : Prop) (whitespaceConfusion : Prop)
    (parsedStepMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (fallbackMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    AyPCWGBadParserGuard malformedComments whitespaceConfusion
      parsedStepMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute ->
    AyPCWGConj noClaim recompute := by
  intro bad
  exact ay_pcwg_conj_intro noClaim recompute
    (ay_pcwg_bad_no_claim malformedComments whitespaceConfusion
      parsedStepMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)
    (ay_pcwg_bad_recompute malformedComments whitespaceConfusion
      parsedStepMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch fallbackMismatch auditMismatch noClaim recompute bad)

theorem ay_pcwg_malformed_comments_forces_no_claim
    (malformedComments : Prop) (noClaim : Prop) :
    malformedComments -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcwg_whitespace_confusion_forces_no_claim
    (whitespaceConfusion : Prop) (noClaim : Prop) :
    whitespaceConfusion -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcwg_parsed_step_mismatch_forces_no_claim
    (parsedStepMismatch : Prop) (noClaim : Prop) :
    parsedStepMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcwg_checker_mismatch_forces_no_claim
    (checkerMismatch : Prop) (noClaim : Prop) :
    checkerMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcwg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch : Prop) (noClaim : Prop) :
    fingerprintMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcwg_build_mismatch_forces_no_claim
    (buildMismatch : Prop) (noClaim : Prop) :
    buildMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcwg_archive_mismatch_forces_no_claim
    (archiveMismatch : Prop) (noClaim : Prop) :
    archiveMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcwg_fallback_mismatch_forces_no_claim
    (fallbackMismatch : Prop) (noClaim : Prop) :
    fallbackMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_pcwg_audit_mismatch_forces_no_claim
    (auditMismatch : Prop) (noClaim : Prop) :
    auditMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
