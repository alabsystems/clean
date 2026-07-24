-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Input-clause origin guard soundness for ay sequential-main SAT-COMP UNSAT
-- proof publication. Propositions stand for original formula digests, input
-- clause ID maps, proof digests, addition/deletion ledgers, antecedent origin
-- ledgers, proof replay, empty-clause reachability witnesses, checker
-- transcripts, benchmark fingerprints, build/archive evidence, fallback
-- no-claim paths, audit transcripts, and fail-closed recompute diagnostics.

def ay_icog_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_icog_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_icog_map (source : Prop) (target : Prop) :=
  source -> target

def ay_icog_accepted_evidence
    (originalFormulaDigest : Prop) (inputClauseIdMap : Prop)
    (proofDigest : Prop) (additionDeletionLedger : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (originalFormulaDigest ->
      inputClauseIdMap ->
      proofDigest ->
      additionDeletionLedger ->
      antecedentOriginLedger ->
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

def ay_icog_origin_replay_composition
    (originalFormulaDigest : Prop) (inputClauseIdMap : Prop)
    (proofDigest : Prop) (additionDeletionLedger : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop) :=
  ay_icog_conj
    (ay_icog_map originalFormulaDigest inputClauseIdMap)
    (ay_icog_conj
      (ay_icog_map inputClauseIdMap proofDigest)
      (ay_icog_conj
        (ay_icog_map proofDigest additionDeletionLedger)
        (ay_icog_conj
          (ay_icog_map additionDeletionLedger antecedentOriginLedger)
          (ay_icog_conj
            (ay_icog_map antecedentOriginLedger proofReplay)
            (ay_icog_conj
              (ay_icog_map proofReplay emptyClauseReachabilityWitness)
              (ay_icog_map emptyClauseReachabilityWitness originalUnsat)))))))

def ay_icog_publication
    (originalFormulaDigest : Prop) (inputClauseIdMap : Prop)
    (proofDigest : Prop) (additionDeletionLedger : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :=
  ay_icog_conj
    (ay_icog_accepted_evidence originalFormulaDigest inputClauseIdMap
      proofDigest additionDeletionLedger antecedentOriginLedger proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat)
    originalUnsat

def ay_icog_failure_reason
    (originMismatch : Prop) (mapMismatch : Prop) (digestMismatch : Prop)
    (ledgerMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (originMismatch -> result) ->
    (mapMismatch -> result) ->
    (digestMismatch -> result) ->
    (ledgerMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_icog_bad_guard
    (originMismatch : Prop) (mapMismatch : Prop) (digestMismatch : Prop)
    (ledgerMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_icog_conj
    (ay_icog_conj noClaim recompute)
    (ay_icog_failure_reason originMismatch mapMismatch digestMismatch
      ledgerMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch)

def ay_icog_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_icog_disj noClaim (ay_icog_disj originalUnsat publicSat)

theorem ay_icog_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_icog_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_icog_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_icog_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_icog_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_icog_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_icog_build_accepted_evidence
    (originalFormulaDigest : Prop) (inputClauseIdMap : Prop)
    (proofDigest : Prop) (additionDeletionLedger : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    originalFormulaDigest ->
    inputClauseIdMap ->
    proofDigest ->
    additionDeletionLedger ->
    antecedentOriginLedger ->
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
    ay_icog_accepted_evidence originalFormulaDigest inputClauseIdMap
      proofDigest additionDeletionLedger antecedentOriginLedger proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat := by
  intro hOriginalDigest hMap hProofDigest hLedger hOrigin hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hOriginal result publish
  exact publish hOriginalDigest hMap hProofDigest hLedger hOrigin hReplay
    hEmpty hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_icog_empty_clause_reachable
    (originalFormulaDigest : Prop) (inputClauseIdMap : Prop)
    (proofDigest : Prop) (additionDeletionLedger : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_icog_accepted_evidence originalFormulaDigest inputClauseIdMap
      proofDigest additionDeletionLedger antecedentOriginLedger proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hOriginalDigest _hMap _hProofDigest _hLedger _hOrigin _hReplay
      hEmpty _hTranscript _hChecker _hFingerprint _hFingerprintAccepted
      _hBuild _hBuildAccepted _hArchive _hFallback _hAudit _hOriginal =>
      hEmpty)

theorem ay_icog_original_unsat
    (originalFormulaDigest : Prop) (inputClauseIdMap : Prop)
    (proofDigest : Prop) (additionDeletionLedger : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_icog_accepted_evidence originalFormulaDigest inputClauseIdMap
      proofDigest additionDeletionLedger antecedentOriginLedger proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hOriginalDigest _hMap _hProofDigest _hLedger _hOrigin _hReplay
      _hEmpty _hTranscript _hChecker _hFingerprint _hFingerprintAccepted
      _hBuild _hBuildAccepted _hArchive _hFallback _hAudit hOriginal =>
      hOriginal)

theorem ay_icog_origin_replay_composes_to_original
    (originalFormulaDigest : Prop) (inputClauseIdMap : Prop)
    (proofDigest : Prop) (additionDeletionLedger : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop) :
    ay_icog_origin_replay_composition originalFormulaDigest inputClauseIdMap
      proofDigest additionDeletionLedger antecedentOriginLedger proofReplay
      emptyClauseReachabilityWitness originalUnsat ->
    originalFormulaDigest ->
    originalUnsat := by
  intro composition hOriginalDigest
  exact composition originalUnsat
    (fun original_to_map rest =>
      rest originalUnsat
        (fun map_to_proof rest2 =>
          rest2 originalUnsat
            (fun proof_to_ledger rest3 =>
              rest3 originalUnsat
                (fun ledger_to_origin rest4 =>
                  rest4 originalUnsat
                    (fun origin_to_replay rest5 =>
                      rest5 originalUnsat
                        (fun replay_to_empty empty_to_original =>
                          empty_to_original
                            (replay_to_empty
                              (origin_to_replay
                                (ledger_to_origin
                                  (proof_to_ledger
                                    (map_to_proof
                                      (original_to_map
                                        hOriginalDigest))))))))))))

theorem ay_icog_publication_sound
    (originalFormulaDigest : Prop) (inputClauseIdMap : Prop)
    (proofDigest : Prop) (additionDeletionLedger : Prop)
    (antecedentOriginLedger : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) :
    ay_icog_publication originalFormulaDigest inputClauseIdMap proofDigest
      additionDeletionLedger antecedentOriginLedger proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_icog_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_icog_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_icog_disj_right noClaim (ay_icog_disj originalUnsat publicSat)
    (ay_icog_disj_left originalUnsat publicSat hOriginal)

theorem ay_icog_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_icog_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_icog_disj_left noClaim (ay_icog_disj originalUnsat publicSat)
    hNoClaim

theorem ay_icog_bad_no_claim
    (originMismatch : Prop) (mapMismatch : Prop) (digestMismatch : Prop)
    (ledgerMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_icog_bad_guard originMismatch mapMismatch digestMismatch ledgerMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_icog_bad_recompute
    (originMismatch : Prop) (mapMismatch : Prop) (digestMismatch : Prop)
    (ledgerMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_icog_bad_guard originMismatch mapMismatch digestMismatch ledgerMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_icog_failed_guard_cannot_bless_unsat
    (originMismatch : Prop) (mapMismatch : Prop) (digestMismatch : Prop)
    (ledgerMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_icog_bad_guard originMismatch mapMismatch digestMismatch ledgerMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    ay_icog_disj noClaim originalUnsat := by
  intro bad
  exact ay_icog_disj_left noClaim originalUnsat
    (ay_icog_bad_no_claim originMismatch mapMismatch digestMismatch
      ledgerMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute bad)

theorem ay_icog_failed_guard_cannot_create_public_sat
    (originMismatch : Prop) (mapMismatch : Prop) (digestMismatch : Prop)
    (ledgerMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_icog_bad_guard originMismatch mapMismatch digestMismatch ledgerMismatch
      antecedentMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    ay_icog_disj noClaim publicSat := by
  intro bad
  exact ay_icog_disj_left noClaim publicSat
    (ay_icog_bad_no_claim originMismatch mapMismatch digestMismatch
      ledgerMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch
      noClaim recompute bad)

theorem ay_icog_failure_forces_no_claim
    (originMismatch : Prop) (mapMismatch : Prop) (digestMismatch : Prop)
    (ledgerMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_icog_failure_reason originMismatch mapMismatch digestMismatch
      ledgerMismatch antecedentMismatch replayMismatch checkerMismatch
      fingerprintMismatch buildMismatch archiveMismatch auditMismatch ->
    (originMismatch -> noClaim) ->
    (mapMismatch -> noClaim) ->
    (digestMismatch -> noClaim) ->
    (ledgerMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure origin_to_no_claim map_to_no_claim digest_to_no_claim
  intro ledger_to_no_claim antecedent_to_no_claim replay_to_no_claim
  intro checker_to_no_claim fingerprint_to_no_claim build_to_no_claim
  intro archive_to_no_claim audit_to_no_claim
  exact failure noClaim origin_to_no_claim map_to_no_claim digest_to_no_claim
    ledger_to_no_claim antecedent_to_no_claim replay_to_no_claim
    checker_to_no_claim fingerprint_to_no_claim build_to_no_claim
    archive_to_no_claim audit_to_no_claim

theorem ay_icog_origin_mismatch_forces_no_claim
    (originMismatch noClaim : Prop) :
    originMismatch -> (originMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_icog_map_mismatch_forces_no_claim
    (mapMismatch noClaim : Prop) :
    mapMismatch -> (mapMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_icog_digest_mismatch_forces_no_claim
    (digestMismatch noClaim : Prop) :
    digestMismatch -> (digestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_icog_ledger_mismatch_forces_no_claim
    (ledgerMismatch noClaim : Prop) :
    ledgerMismatch -> (ledgerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_icog_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch -> (antecedentMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_icog_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_icog_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_icog_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_icog_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_icog_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_icog_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
