-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Resolution-pivot guard soundness for ay sequential-main SAT-COMP UNSAT
-- proof publication. The propositions below stand for proof text digests,
-- parsed-step ledgers, pivot choices, antecedent availability, resolvent
-- reconstruction, tautology/deletion policy, empty-clause reachability,
-- checker transcripts, benchmark fingerprints, solver build evidence,
-- archive manifests, fallback no-claim paths, audit transcripts, and
-- fail-closed recompute diagnostics.

def ay_rpvg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_rpvg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_rpvg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_rpvg_accepted_evidence
    (proofTextDigest : Prop) (parsedStepLedger : Prop)
    (pivotSelectionWitness : Prop) (antecedentAvailability : Prop)
    (resolventReconstruction : Prop) (tautologyDeletionPolicy : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofTextDigest ->
      parsedStepLedger ->
      pivotSelectionWitness ->
      antecedentAvailability ->
      resolventReconstruction ->
      tautologyDeletionPolicy ->
      emptyClauseReachable ->
      checkerTranscript ->
      checkerAccepted ->
      benchmarkFingerprint ->
      fingerprintAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      archiveManifest ->
      fallbackNoClaim ->
      auditTranscript ->
      visibleUnsat ->
      originalUnsat ->
      result) ->
    result

def ay_rpvg_pivot_replay_composition
    (proofTextDigest : Prop) (parsedStepLedger : Prop)
    (pivotSelectionWitness : Prop) (antecedentAvailability : Prop)
    (resolventReconstruction : Prop) (tautologyDeletionPolicy : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  ay_rpvg_conj
    (ay_rpvg_map proofTextDigest parsedStepLedger)
    (ay_rpvg_conj
      (ay_rpvg_map parsedStepLedger pivotSelectionWitness)
      (ay_rpvg_conj
        (ay_rpvg_map pivotSelectionWitness antecedentAvailability)
        (ay_rpvg_conj
          (ay_rpvg_map antecedentAvailability resolventReconstruction)
          (ay_rpvg_conj
            (ay_rpvg_map resolventReconstruction tautologyDeletionPolicy)
            (ay_rpvg_conj
              (ay_rpvg_map tautologyDeletionPolicy emptyClauseReachable)
              (ay_rpvg_conj
                (ay_rpvg_map emptyClauseReachable visibleUnsat)
                (ay_rpvg_map visibleUnsat originalUnsat)))))))

def ay_rpvg_publication
    (proofTextDigest : Prop) (parsedStepLedger : Prop)
    (pivotSelectionWitness : Prop) (antecedentAvailability : Prop)
    (resolventReconstruction : Prop) (tautologyDeletionPolicy : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  ay_rpvg_conj
    (ay_rpvg_accepted_evidence proofTextDigest parsedStepLedger
      pivotSelectionWitness antecedentAvailability resolventReconstruction
      tautologyDeletionPolicy emptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript visibleUnsat originalUnsat)
    originalUnsat

def ay_rpvg_failure_reason
    (digestMismatch : Prop) (parseMismatch : Prop) (pivotMismatch : Prop)
    (antecedentMismatch : Prop) (resolventMismatch : Prop)
    (policyMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (parseMismatch -> result) ->
    (pivotMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (resolventMismatch -> result) ->
    (policyMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_rpvg_bad_guard
    (digestMismatch : Prop) (parseMismatch : Prop) (pivotMismatch : Prop)
    (antecedentMismatch : Prop) (resolventMismatch : Prop)
    (policyMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  ay_rpvg_conj
    (ay_rpvg_conj noClaim recompute)
    (ay_rpvg_failure_reason digestMismatch parseMismatch pivotMismatch
      antecedentMismatch resolventMismatch policyMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch)

def ay_rpvg_public_report (noClaim : Prop) (originalUnsat : Prop) :=
  ay_rpvg_disj noClaim originalUnsat

theorem ay_rpvg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_rpvg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_rpvg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_rpvg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_rpvg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_rpvg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_rpvg_build_accepted_evidence
    (proofTextDigest : Prop) (parsedStepLedger : Prop)
    (pivotSelectionWitness : Prop) (antecedentAvailability : Prop)
    (resolventReconstruction : Prop) (tautologyDeletionPolicy : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    proofTextDigest ->
    parsedStepLedger ->
    pivotSelectionWitness ->
    antecedentAvailability ->
    resolventReconstruction ->
    tautologyDeletionPolicy ->
    emptyClauseReachable ->
    checkerTranscript ->
    checkerAccepted ->
    benchmarkFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    archiveManifest ->
    fallbackNoClaim ->
    auditTranscript ->
    visibleUnsat ->
    originalUnsat ->
    ay_rpvg_accepted_evidence proofTextDigest parsedStepLedger
      pivotSelectionWitness antecedentAvailability resolventReconstruction
      tautologyDeletionPolicy emptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript visibleUnsat originalUnsat := by
  intro hDigest hParsed hPivot hAntecedent hResolvent hPolicy hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hVisible hOriginal
  intro result publish
  exact publish hDigest hParsed hPivot hAntecedent hResolvent hPolicy hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hVisible hOriginal

theorem ay_rpvg_empty_clause_reachable
    (proofTextDigest : Prop) (parsedStepLedger : Prop)
    (pivotSelectionWitness : Prop) (antecedentAvailability : Prop)
    (resolventReconstruction : Prop) (tautologyDeletionPolicy : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    ay_rpvg_accepted_evidence proofTextDigest parsedStepLedger
      pivotSelectionWitness antecedentAvailability resolventReconstruction
      tautologyDeletionPolicy emptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript visibleUnsat originalUnsat ->
    emptyClauseReachable := by
  intro accepted
  exact accepted emptyClauseReachable
    (fun _hDigest _hParsed _hPivot _hAntecedent _hResolvent _hPolicy hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hEmpty)

theorem ay_rpvg_checker_transcript
    (proofTextDigest : Prop) (parsedStepLedger : Prop)
    (pivotSelectionWitness : Prop) (antecedentAvailability : Prop)
    (resolventReconstruction : Prop) (tautologyDeletionPolicy : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    ay_rpvg_accepted_evidence proofTextDigest parsedStepLedger
      pivotSelectionWitness antecedentAvailability resolventReconstruction
      tautologyDeletionPolicy emptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript visibleUnsat originalUnsat ->
    checkerTranscript := by
  intro accepted
  exact accepted checkerTranscript
    (fun _hDigest _hParsed _hPivot _hAntecedent _hResolvent _hPolicy _hEmpty
      hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible _hOriginal =>
      hTranscript)

theorem ay_rpvg_original_unsat
    (proofTextDigest : Prop) (parsedStepLedger : Prop)
    (pivotSelectionWitness : Prop) (antecedentAvailability : Prop)
    (resolventReconstruction : Prop) (tautologyDeletionPolicy : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    ay_rpvg_accepted_evidence proofTextDigest parsedStepLedger
      pivotSelectionWitness antecedentAvailability resolventReconstruction
      tautologyDeletionPolicy emptyClauseReachable checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hParsed _hPivot _hAntecedent _hResolvent _hPolicy _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hVisible hOriginal =>
      hOriginal)

theorem ay_rpvg_pivot_replay_composes_to_original
    (proofTextDigest : Prop) (parsedStepLedger : Prop)
    (pivotSelectionWitness : Prop) (antecedentAvailability : Prop)
    (resolventReconstruction : Prop) (tautologyDeletionPolicy : Prop)
    (emptyClauseReachable : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    proofTextDigest ->
    ay_rpvg_pivot_replay_composition proofTextDigest parsedStepLedger
      pivotSelectionWitness antecedentAvailability resolventReconstruction
      tautologyDeletionPolicy emptyClauseReachable visibleUnsat originalUnsat ->
    originalUnsat := by
  intro hDigest
  intro composed
  exact composed originalUnsat
    (fun digest_to_parsed rest1 =>
      rest1 originalUnsat
        (fun parsed_to_pivot rest2 =>
          rest2 originalUnsat
            (fun pivot_to_antecedent rest3 =>
              rest3 originalUnsat
                (fun antecedent_to_resolvent rest4 =>
                  rest4 originalUnsat
                    (fun resolvent_to_policy rest5 =>
                      rest5 originalUnsat
                        (fun policy_to_empty rest6 =>
                          rest6 originalUnsat
                            (fun empty_to_visible visible_to_original =>
                              visible_to_original
                                (empty_to_visible
                                  (policy_to_empty
                                    (resolvent_to_policy
                                      (antecedent_to_resolvent
                                        (pivot_to_antecedent
                                          (parsed_to_pivot
                                            (digest_to_parsed
                                              hDigest))))))))))))))

theorem ay_rpvg_publication_sound
    (proofTextDigest : Prop) (parsedStepLedger : Prop)
    (pivotSelectionWitness : Prop) (antecedentAvailability : Prop)
    (resolventReconstruction : Prop) (tautologyDeletionPolicy : Prop)
    (emptyClauseReachable : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    ay_rpvg_publication proofTextDigest parsedStepLedger pivotSelectionWitness
      antecedentAvailability resolventReconstruction tautologyDeletionPolicy
      emptyClauseReachable checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat (fun _accepted unsat => unsat)

theorem ay_rpvg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> ay_rpvg_public_report noClaim originalUnsat := by
  intro unsat
  exact ay_rpvg_disj_right noClaim originalUnsat unsat

theorem ay_rpvg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> ay_rpvg_public_report noClaim originalUnsat := by
  intro no_claim
  exact ay_rpvg_disj_left noClaim originalUnsat no_claim

theorem ay_rpvg_bad_no_claim
    (digestMismatch : Prop) (parseMismatch : Prop) (pivotMismatch : Prop)
    (antecedentMismatch : Prop) (resolventMismatch : Prop)
    (policyMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_rpvg_bad_guard digestMismatch parseMismatch pivotMismatch
      antecedentMismatch resolventMismatch policyMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun closed _reason =>
      closed noClaim (fun no_claim _recheck => no_claim))

theorem ay_rpvg_bad_recompute
    (digestMismatch : Prop) (parseMismatch : Prop) (pivotMismatch : Prop)
    (antecedentMismatch : Prop) (resolventMismatch : Prop)
    (policyMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_rpvg_bad_guard digestMismatch parseMismatch pivotMismatch
      antecedentMismatch resolventMismatch policyMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun closed _reason =>
      closed recompute (fun _no_claim recheck => recheck))

theorem ay_rpvg_failed_pivot_guard_cannot_bless_unsat
    (digestMismatch : Prop) (parseMismatch : Prop) (pivotMismatch : Prop)
    (antecedentMismatch : Prop) (resolventMismatch : Prop)
    (policyMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    ay_rpvg_bad_guard digestMismatch parseMismatch pivotMismatch
      antecedentMismatch resolventMismatch policyMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_rpvg_public_report noClaim originalUnsat := by
  intro bad
  exact ay_rpvg_public_no_claim_report noClaim originalUnsat
    (ay_rpvg_bad_no_claim digestMismatch parseMismatch pivotMismatch
      antecedentMismatch resolventMismatch policyMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_rpvg_failed_pivot_guard_cannot_create_public_sat
    (digestMismatch : Prop) (parseMismatch : Prop) (pivotMismatch : Prop)
    (antecedentMismatch : Prop) (resolventMismatch : Prop)
    (policyMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (publicSat : Prop) :
    ay_rpvg_bad_guard digestMismatch parseMismatch pivotMismatch
      antecedentMismatch resolventMismatch policyMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact ay_rpvg_bad_no_claim digestMismatch parseMismatch pivotMismatch
    antecedentMismatch resolventMismatch policyMismatch reachabilityMismatch
    checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
    auditMismatch noClaim recompute bad

theorem ay_rpvg_failure_forces_no_claim
    (digestMismatch : Prop) (parseMismatch : Prop) (pivotMismatch : Prop)
    (antecedentMismatch : Prop) (resolventMismatch : Prop)
    (policyMismatch : Prop) (reachabilityMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_rpvg_bad_guard digestMismatch parseMismatch pivotMismatch
      antecedentMismatch resolventMismatch policyMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_rpvg_conj noClaim recompute := by
  intro bad
  exact ay_rpvg_conj_intro noClaim recompute
    (ay_rpvg_bad_no_claim digestMismatch parseMismatch pivotMismatch
      antecedentMismatch resolventMismatch policyMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)
    (ay_rpvg_bad_recompute digestMismatch parseMismatch pivotMismatch
      antecedentMismatch resolventMismatch policyMismatch reachabilityMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_rpvg_digest_mismatch_forces_no_claim
    (digestMismatch : Prop) (noClaim : Prop) :
    digestMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_rpvg_parse_mismatch_forces_no_claim
    (parseMismatch : Prop) (noClaim : Prop) :
    parseMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_rpvg_pivot_mismatch_forces_no_claim
    (pivotMismatch : Prop) (noClaim : Prop) :
    pivotMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_rpvg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch : Prop) (noClaim : Prop) :
    antecedentMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_rpvg_resolvent_mismatch_forces_no_claim
    (resolventMismatch : Prop) (noClaim : Prop) :
    resolventMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_rpvg_policy_mismatch_forces_no_claim
    (policyMismatch : Prop) (noClaim : Prop) :
    policyMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_rpvg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch : Prop) (noClaim : Prop) :
    reachabilityMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_rpvg_checker_mismatch_forces_no_claim
    (checkerMismatch : Prop) (noClaim : Prop) :
    checkerMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_rpvg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch : Prop) (noClaim : Prop) :
    fingerprintMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_rpvg_build_mismatch_forces_no_claim
    (buildMismatch : Prop) (noClaim : Prop) :
    buildMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_rpvg_archive_mismatch_forces_no_claim
    (archiveMismatch : Prop) (noClaim : Prop) :
    archiveMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim

theorem ay_rpvg_audit_mismatch_forces_no_claim
    (auditMismatch : Prop) (noClaim : Prop) :
    auditMismatch -> noClaim -> noClaim := by
  intro _failure no_claim
  exact no_claim
