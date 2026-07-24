-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Proof clause-order/permutation guard soundness for ay sequential-main
-- SAT-COMP UNSAT proof publication. The propositions below model proof
-- digests, parsed line ledgers, permutation manifests, antecedent
-- availability, proof replay, empty-clause reachability, checker transcripts,
-- benchmark fingerprints, build/archive evidence, fallback no-claim paths,
-- audit transcripts, and fail-closed recompute diagnostics.

def ay_copg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_copg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_copg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_copg_accepted_evidence
    (proofDigest : Prop) (parsedLineLedger : Prop)
    (clauseOrderPermutationManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (proofDigest ->
      parsedLineLedger ->
      clauseOrderPermutationManifest ->
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

def ay_copg_permutation_replay_composition
    (proofDigest : Prop) (parsedLineLedger : Prop)
    (clauseOrderPermutationManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop) :=
  ay_copg_conj
    (ay_copg_map proofDigest parsedLineLedger)
    (ay_copg_conj
      (ay_copg_map parsedLineLedger clauseOrderPermutationManifest)
      (ay_copg_conj
        (ay_copg_map clauseOrderPermutationManifest
          antecedentAvailabilityWitness)
        (ay_copg_conj
          (ay_copg_map antecedentAvailabilityWitness proofReplay)
          (ay_copg_conj
            (ay_copg_map proofReplay emptyClauseReachabilityWitness)
            (ay_copg_map emptyClauseReachabilityWitness originalUnsat))))))

def ay_copg_publication
    (proofDigest : Prop) (parsedLineLedger : Prop)
    (clauseOrderPermutationManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  ay_copg_conj
    (ay_copg_accepted_evidence proofDigest parsedLineLedger
      clauseOrderPermutationManifest antecedentAvailabilityWitness
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat)
    originalUnsat

def ay_copg_failure_reason
    (orderMismatch : Prop) (permutationMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (orderMismatch -> result) ->
    (permutationMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_copg_bad_guard
    (orderMismatch : Prop) (permutationMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_copg_conj
    (ay_copg_conj noClaim recompute)
    (ay_copg_failure_reason orderMismatch permutationMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch)

def ay_copg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_copg_disj noClaim (ay_copg_disj originalUnsat publicSat)

theorem ay_copg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_copg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_copg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_copg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_copg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_copg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_copg_build_accepted_evidence
    (proofDigest : Prop) (parsedLineLedger : Prop)
    (clauseOrderPermutationManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    proofDigest ->
    parsedLineLedger ->
    clauseOrderPermutationManifest ->
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
    ay_copg_accepted_evidence proofDigest parsedLineLedger
      clauseOrderPermutationManifest antecedentAvailabilityWitness
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat := by
  intro hDigest hLedger hPermutation hAntecedent hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hOriginal result publish
  exact publish hDigest hLedger hPermutation hAntecedent hReplay hEmpty
    hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_copg_empty_clause_reachable
    (proofDigest : Prop) (parsedLineLedger : Prop)
    (clauseOrderPermutationManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_copg_accepted_evidence proofDigest parsedLineLedger
      clauseOrderPermutationManifest antecedentAvailabilityWitness
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hDigest _hLedger _hPermutation _hAntecedent _hReplay hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_copg_original_unsat
    (proofDigest : Prop) (parsedLineLedger : Prop)
    (clauseOrderPermutationManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_copg_accepted_evidence proofDigest parsedLineLedger
      clauseOrderPermutationManifest antecedentAvailabilityWitness
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hLedger _hPermutation _hAntecedent _hReplay _hEmpty
      _hTranscript _hChecker _hFingerprint _hFingerprintAccepted _hBuild
      _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_copg_permutation_replay_composes_to_original
    (proofDigest : Prop) (parsedLineLedger : Prop)
    (clauseOrderPermutationManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop) :
    ay_copg_permutation_replay_composition proofDigest parsedLineLedger
      clauseOrderPermutationManifest antecedentAvailabilityWitness proofReplay
      emptyClauseReachabilityWitness originalUnsat ->
    proofDigest ->
    originalUnsat := by
  intro composition hDigest
  exact composition originalUnsat
    (fun digest_to_ledger rest =>
      rest originalUnsat
        (fun ledger_to_permutation rest2 =>
          rest2 originalUnsat
            (fun permutation_to_antecedent rest3 =>
              rest3 originalUnsat
                (fun antecedent_to_replay rest4 =>
                  rest4 originalUnsat
                    (fun replay_to_empty empty_to_original =>
                      empty_to_original
                        (replay_to_empty
                          (antecedent_to_replay
                            (permutation_to_antecedent
                              (ledger_to_permutation
                                (digest_to_ledger hDigest))))))))))

theorem ay_copg_publication_sound
    (proofDigest : Prop) (parsedLineLedger : Prop)
    (clauseOrderPermutationManifest : Prop)
    (antecedentAvailabilityWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_copg_publication proofDigest parsedLineLedger
      clauseOrderPermutationManifest antecedentAvailabilityWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_copg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_copg_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_copg_disj_right noClaim (ay_copg_disj originalUnsat publicSat)
    (ay_copg_disj_left originalUnsat publicSat hUnsat)

theorem ay_copg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_copg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_copg_disj_left noClaim
    (ay_copg_disj originalUnsat publicSat) hNoClaim

theorem ay_copg_bad_no_claim
    (orderMismatch : Prop) (permutationMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_copg_bad_guard orderMismatch permutationMismatch antecedentMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_copg_bad_recompute
    (orderMismatch : Prop) (permutationMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_copg_bad_guard orderMismatch permutationMismatch antecedentMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_copg_failed_guard_cannot_bless_unsat
    (orderMismatch : Prop) (permutationMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicUnsat : Prop) :
    ay_copg_bad_guard orderMismatch permutationMismatch antecedentMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_copg_map noClaim (publicUnsat -> recompute) := by
  intro bad hNoClaim _hPublicUnsat
  exact ay_copg_bad_recompute orderMismatch permutationMismatch
    antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
    buildMismatch archiveMismatch auditMismatch noClaim recompute bad

theorem ay_copg_failed_guard_cannot_create_public_sat
    (orderMismatch : Prop) (permutationMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_copg_bad_guard orderMismatch permutationMismatch antecedentMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_copg_map noClaim (publicSat -> recompute) := by
  intro bad hNoClaim _hPublicSat
  exact ay_copg_bad_recompute orderMismatch permutationMismatch
    antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
    buildMismatch archiveMismatch auditMismatch noClaim recompute bad

theorem ay_copg_failure_forces_no_claim
    (orderMismatch : Prop) (permutationMismatch : Prop)
    (antecedentMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) :
    ay_copg_failure_reason orderMismatch permutationMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch ->
    (orderMismatch -> noClaim) ->
    (permutationMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason order_to_no_claim permutation_to_no_claim
  intro antecedent_to_no_claim replay_to_no_claim checker_to_no_claim
  intro fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
  intro audit_to_no_claim
  exact reason noClaim order_to_no_claim permutation_to_no_claim
    antecedent_to_no_claim replay_to_no_claim checker_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_copg_order_mismatch_forces_no_claim
    (orderMismatch noClaim : Prop) :
    orderMismatch ->
    (orderMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_copg_permutation_mismatch_forces_no_claim
    (permutationMismatch noClaim : Prop) :
    permutationMismatch ->
    (permutationMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_copg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch ->
    (antecedentMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_copg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch ->
    (replayMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_copg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch ->
    (checkerMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_copg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch ->
    (fingerprintMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_copg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_copg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_copg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
