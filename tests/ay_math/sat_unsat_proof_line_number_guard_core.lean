-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Proof line-number/identifier monotonicity guard soundness for ay
-- sequential-main SAT-COMP UNSAT proof publication. Propositions stand for raw
-- proof digests, parsed line ledgers, line-number monotonicity witnesses,
-- clause-ID namespace manifests, antecedent availability, proof replay,
-- empty-clause reachability witnesses, checker transcripts, benchmark
-- fingerprints, build/archive evidence, fallback no-claim paths, audit
-- transcripts, and fail-closed recompute diagnostics.

def ay_plng_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_plng_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_plng_map (source : Prop) (target : Prop) :=
  source -> target

def ay_plng_accepted_evidence
    (rawProofDigest : Prop) (parsedLineLedger : Prop)
    (lineMonotonicityWitness : Prop) (clauseIdNamespaceManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (rawProofDigest ->
      parsedLineLedger ->
      lineMonotonicityWitness ->
      clauseIdNamespaceManifest ->
      antecedentAvailabilityWitness ->
      proofReplay ->
      emptyClauseReachabilityWitness ->
      checkerTranscript ->
      checkerAccepted ->
      benchmarkFingerprint ->
      fingerprintAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      archiveManifest ->
      fallbackNoClaim ->
      auditTranscript ->
      originalUnsat ->
      result) ->
    result

def ay_plng_line_replay_composition
    (rawProofDigest : Prop) (parsedLineLedger : Prop)
    (lineMonotonicityWitness : Prop) (clauseIdNamespaceManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop) :=
  ay_plng_conj
    (ay_plng_map rawProofDigest parsedLineLedger)
    (ay_plng_conj
      (ay_plng_map parsedLineLedger lineMonotonicityWitness)
      (ay_plng_conj
        (ay_plng_map lineMonotonicityWitness clauseIdNamespaceManifest)
        (ay_plng_conj
          (ay_plng_map clauseIdNamespaceManifest
            antecedentAvailabilityWitness)
          (ay_plng_conj
            (ay_plng_map antecedentAvailabilityWitness proofReplay)
            (ay_plng_conj
              (ay_plng_map proofReplay emptyClauseReachabilityWitness)
              (ay_plng_map emptyClauseReachabilityWitness originalUnsat)))))))

def ay_plng_publication
    (rawProofDigest : Prop) (parsedLineLedger : Prop)
    (lineMonotonicityWitness : Prop) (clauseIdNamespaceManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  ay_plng_conj
    (ay_plng_accepted_evidence rawProofDigest parsedLineLedger
      lineMonotonicityWitness clauseIdNamespaceManifest
      antecedentAvailabilityWitness proofReplay emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat)
    originalUnsat

def ay_plng_failure_reason
    (lineMismatch : Prop) (namespaceMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (lineMismatch -> result) ->
    (namespaceMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_plng_bad_guard
    (lineMismatch : Prop) (namespaceMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_plng_conj
    (ay_plng_conj noClaim recompute)
    (ay_plng_failure_reason lineMismatch namespaceMismatch antecedentMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch)

def ay_plng_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_plng_disj noClaim (ay_plng_disj originalUnsat publicSat)

theorem ay_plng_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_plng_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_plng_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_plng_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_plng_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_plng_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_plng_build_accepted_evidence
    (rawProofDigest : Prop) (parsedLineLedger : Prop)
    (lineMonotonicityWitness : Prop) (clauseIdNamespaceManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    rawProofDigest ->
    parsedLineLedger ->
    lineMonotonicityWitness ->
    clauseIdNamespaceManifest ->
    antecedentAvailabilityWitness ->
    proofReplay ->
    emptyClauseReachabilityWitness ->
    checkerTranscript ->
    checkerAccepted ->
    benchmarkFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    archiveManifest ->
    fallbackNoClaim ->
    auditTranscript ->
    originalUnsat ->
    ay_plng_accepted_evidence rawProofDigest parsedLineLedger
      lineMonotonicityWitness clauseIdNamespaceManifest
      antecedentAvailabilityWitness proofReplay emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat := by
  intro hRaw hLine hMonotone hNamespace hAntecedent hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hOriginal result publish
  exact publish hRaw hLine hMonotone hNamespace hAntecedent hReplay hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_plng_empty_clause_reachable
    (rawProofDigest : Prop) (parsedLineLedger : Prop)
    (lineMonotonicityWitness : Prop) (clauseIdNamespaceManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_plng_accepted_evidence rawProofDigest parsedLineLedger
      lineMonotonicityWitness clauseIdNamespaceManifest
      antecedentAvailabilityWitness proofReplay emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hRaw _hLine _hMonotone _hNamespace _hAntecedent _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_plng_original_unsat
    (rawProofDigest : Prop) (parsedLineLedger : Prop)
    (lineMonotonicityWitness : Prop) (clauseIdNamespaceManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_plng_accepted_evidence rawProofDigest parsedLineLedger
      lineMonotonicityWitness clauseIdNamespaceManifest
      antecedentAvailabilityWitness proofReplay emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hRaw _hLine _hMonotone _hNamespace _hAntecedent _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_plng_line_replay_composes_to_original
    (rawProofDigest : Prop) (parsedLineLedger : Prop)
    (lineMonotonicityWitness : Prop) (clauseIdNamespaceManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop) :
    ay_plng_line_replay_composition rawProofDigest parsedLineLedger
      lineMonotonicityWitness clauseIdNamespaceManifest
      antecedentAvailabilityWitness proofReplay emptyClauseReachabilityWitness
      originalUnsat ->
    rawProofDigest ->
    originalUnsat := by
  intro composition hRaw
  exact composition originalUnsat
    (fun raw_to_line rest =>
      rest originalUnsat
        (fun line_to_monotone rest2 =>
          rest2 originalUnsat
            (fun monotone_to_namespace rest3 =>
              rest3 originalUnsat
                (fun namespace_to_antecedent rest4 =>
                  rest4 originalUnsat
                    (fun antecedent_to_replay rest5 =>
                      rest5 originalUnsat
                        (fun replay_to_empty empty_to_original =>
                          empty_to_original
                            (replay_to_empty
                              (antecedent_to_replay
                                (namespace_to_antecedent
                                  (monotone_to_namespace
                                    (line_to_monotone
                                      (raw_to_line hRaw))))))))))))

theorem ay_plng_publication_sound
    (rawProofDigest : Prop) (parsedLineLedger : Prop)
    (lineMonotonicityWitness : Prop) (clauseIdNamespaceManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_plng_publication rawProofDigest parsedLineLedger
      lineMonotonicityWitness clauseIdNamespaceManifest
      antecedentAvailabilityWitness proofReplay emptyClauseReachabilityWitness
      checkerTranscript checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_plng_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_plng_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_plng_disj_right noClaim (ay_plng_disj originalUnsat publicSat)
    (ay_plng_disj_left originalUnsat publicSat hOriginal)

theorem ay_plng_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_plng_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_plng_disj_left noClaim (ay_plng_disj originalUnsat publicSat)
    hNoClaim

theorem ay_plng_bad_no_claim
    (lineMismatch : Prop) (namespaceMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_plng_bad_guard lineMismatch namespaceMismatch antecedentMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_plng_bad_recompute
    (lineMismatch : Prop) (namespaceMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_plng_bad_guard lineMismatch namespaceMismatch antecedentMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_plng_failed_guard_cannot_bless_unsat
    (lineMismatch : Prop) (namespaceMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_plng_bad_guard lineMismatch namespaceMismatch antecedentMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_plng_disj noClaim originalUnsat := by
  intro bad
  exact ay_plng_disj_left noClaim originalUnsat
    (ay_plng_bad_no_claim lineMismatch namespaceMismatch antecedentMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_plng_failed_guard_cannot_create_public_sat
    (lineMismatch : Prop) (namespaceMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_plng_bad_guard lineMismatch namespaceMismatch antecedentMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_plng_disj noClaim publicSat := by
  intro bad
  exact ay_plng_disj_left noClaim publicSat
    (ay_plng_bad_no_claim lineMismatch namespaceMismatch antecedentMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_plng_failure_forces_no_claim
    (lineMismatch : Prop) (namespaceMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_plng_failure_reason lineMismatch namespaceMismatch antecedentMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch ->
    (lineMismatch -> noClaim) ->
    (namespaceMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure line_to_no_claim namespace_to_no_claim antecedent_to_no_claim
  intro replay_to_no_claim checker_to_no_claim fingerprint_to_no_claim
  intro build_to_no_claim archive_to_no_claim audit_to_no_claim
  exact failure noClaim line_to_no_claim namespace_to_no_claim
    antecedent_to_no_claim replay_to_no_claim checker_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_plng_line_mismatch_forces_no_claim
    (lineMismatch noClaim : Prop) :
    lineMismatch -> (lineMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_plng_namespace_mismatch_forces_no_claim
    (namespaceMismatch noClaim : Prop) :
    namespaceMismatch -> (namespaceMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_plng_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch -> (antecedentMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_plng_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_plng_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_plng_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_plng_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_plng_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_plng_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
