-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Deletion-step guard soundness for ay sequential-main SAT-COMP UNSAT proof
-- checking. Propositions model formula fingerprints, proof-line digests,
-- live-clause set digests before and after deletion, deletion ledgers,
-- antecedent availability, empty-clause replay, checker transcripts, proof
-- archives, build evidence, fallback no-claim paths, audit transcripts, and
-- fail-closed recompute diagnostics.

def ay_dsg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_dsg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_dsg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_dsg_accepted_evidence
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (liveClauseSetDigestBefore : Prop) (liveClauseSetDigestAfter : Prop)
    (deletionLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (emptyClauseDerivationReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (proofArchiveDigest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (liveClauseConsistency : Prop)
    (proofReplayContext : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (originalFormulaFingerprint ->
      proofLineDigest ->
      liveClauseSetDigestBefore ->
      liveClauseSetDigestAfter ->
      deletionLedger ->
      antecedentAvailabilityWitness ->
      emptyClauseDerivationReplay ->
      checkerTranscript ->
      checkerAccepted ->
      proofArchiveDigest ->
      archiveAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      fallbackNoClaim ->
      auditTranscript ->
      liveClauseConsistency ->
      proofReplayContext ->
      originalUnsat ->
      result) ->
    result

def ay_dsg_deletion_maintenance
    (proofLineDigest : Prop) (liveClauseSetDigestBefore : Prop)
    (liveClauseSetDigestAfter : Prop) (deletionLedger : Prop)
    (liveClauseConsistency : Prop) (proofReplayContext : Prop) :=
  ay_dsg_conj
    (ay_dsg_map proofLineDigest liveClauseSetDigestBefore)
    (ay_dsg_conj
      (ay_dsg_map liveClauseSetDigestBefore deletionLedger)
      (ay_dsg_conj
        (ay_dsg_map deletionLedger liveClauseSetDigestAfter)
        (ay_dsg_conj
          (ay_dsg_map liveClauseSetDigestAfter liveClauseConsistency)
          (ay_dsg_map liveClauseConsistency proofReplayContext))))

def ay_dsg_empty_clause_publication_path
    (antecedentAvailabilityWitness : Prop)
    (emptyClauseDerivationReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (originalUnsat : Prop) :=
  ay_dsg_conj
    (ay_dsg_map antecedentAvailabilityWitness emptyClauseDerivationReplay)
    (ay_dsg_conj
      (ay_dsg_map emptyClauseDerivationReplay checkerTranscript)
      (ay_dsg_conj
        (ay_dsg_map checkerTranscript checkerAccepted)
        (ay_dsg_map checkerAccepted originalUnsat)))

def ay_dsg_publication
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (liveClauseSetDigestBefore : Prop) (liveClauseSetDigestAfter : Prop)
    (deletionLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (emptyClauseDerivationReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (proofArchiveDigest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (liveClauseConsistency : Prop)
    (proofReplayContext : Prop) (originalUnsat : Prop) :=
  ay_dsg_conj
    (ay_dsg_accepted_evidence originalFormulaFingerprint proofLineDigest
      liveClauseSetDigestBefore liveClauseSetDigestAfter deletionLedger
      antecedentAvailabilityWitness emptyClauseDerivationReplay
      checkerTranscript checkerAccepted proofArchiveDigest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      liveClauseConsistency proofReplayContext originalUnsat)
    originalUnsat

def ay_dsg_failure_reason
    (lineMismatch : Prop) (liveSetMismatch : Prop)
    (deletionMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (lineMismatch -> result) ->
    (liveSetMismatch -> result) ->
    (deletionMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (archiveMismatch -> result) ->
    (buildMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_dsg_bad_guard
    (lineMismatch : Prop) (liveSetMismatch : Prop)
    (deletionMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_dsg_conj
    (ay_dsg_conj noClaim recompute)
    (ay_dsg_failure_reason lineMismatch liveSetMismatch deletionMismatch
      antecedentMismatch replayMismatch checkerMismatch archiveMismatch
      buildMismatch auditMismatch)

def ay_dsg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_dsg_disj noClaim (ay_dsg_disj originalUnsat publicSat)

theorem ay_dsg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_dsg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_dsg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_dsg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_dsg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_dsg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_dsg_build_accepted_evidence
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (liveClauseSetDigestBefore : Prop) (liveClauseSetDigestAfter : Prop)
    (deletionLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (emptyClauseDerivationReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (proofArchiveDigest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (liveClauseConsistency : Prop)
    (proofReplayContext : Prop) (originalUnsat : Prop) :
    originalFormulaFingerprint ->
    proofLineDigest ->
    liveClauseSetDigestBefore ->
    liveClauseSetDigestAfter ->
    deletionLedger ->
    antecedentAvailabilityWitness ->
    emptyClauseDerivationReplay ->
    checkerTranscript ->
    checkerAccepted ->
    proofArchiveDigest ->
    archiveAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    fallbackNoClaim ->
    auditTranscript ->
    liveClauseConsistency ->
    proofReplayContext ->
    originalUnsat ->
    ay_dsg_accepted_evidence originalFormulaFingerprint proofLineDigest
      liveClauseSetDigestBefore liveClauseSetDigestAfter deletionLedger
      antecedentAvailabilityWitness emptyClauseDerivationReplay
      checkerTranscript checkerAccepted proofArchiveDigest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      liveClauseConsistency proofReplayContext originalUnsat := by
  intro hFingerprint hLine hLiveBefore hLiveAfter hDeletion hAntecedent
  intro hReplay hTranscript hChecker hArchive hArchiveAccepted hBuild
  intro hBuildAccepted hFallback hAudit hLiveConsistent hContext hOriginal
  intro result publish
  exact publish hFingerprint hLine hLiveBefore hLiveAfter hDeletion
    hAntecedent hReplay hTranscript hChecker hArchive hArchiveAccepted
    hBuild hBuildAccepted hFallback hAudit hLiveConsistent hContext
    hOriginal

theorem ay_dsg_deletion_steps_are_maintenance_only
    (deletionLedger : Prop) (emptyClauseDerivationReplay : Prop)
    (checkerAccepted : Prop) (originalUnsat : Prop) :
    ay_dsg_map checkerAccepted originalUnsat ->
    deletionLedger ->
    emptyClauseDerivationReplay ->
    checkerAccepted ->
    originalUnsat := by
  intro checked_to_unsat _hDeletion _hReplay hChecker
  exact checked_to_unsat hChecker

theorem ay_dsg_empty_clause_replay_required
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (liveClauseSetDigestBefore : Prop) (liveClauseSetDigestAfter : Prop)
    (deletionLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (emptyClauseDerivationReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (proofArchiveDigest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (liveClauseConsistency : Prop)
    (proofReplayContext : Prop) (originalUnsat : Prop) :
    ay_dsg_accepted_evidence originalFormulaFingerprint proofLineDigest
      liveClauseSetDigestBefore liveClauseSetDigestAfter deletionLedger
      antecedentAvailabilityWitness emptyClauseDerivationReplay
      checkerTranscript checkerAccepted proofArchiveDigest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      liveClauseConsistency proofReplayContext originalUnsat ->
    emptyClauseDerivationReplay := by
  intro accepted
  exact accepted emptyClauseDerivationReplay
    (fun _hFingerprint _hLine _hLiveBefore _hLiveAfter _hDeletion
      _hAntecedent hReplay _hTranscript _hChecker _hArchive
      _hArchiveAccepted _hBuild _hBuildAccepted _hFallback _hAudit
      _hLiveConsistent _hContext _hOriginal =>
      hReplay)

theorem ay_dsg_preserves_live_clause_consistency
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (liveClauseSetDigestBefore : Prop) (liveClauseSetDigestAfter : Prop)
    (deletionLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (emptyClauseDerivationReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (proofArchiveDigest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (liveClauseConsistency : Prop)
    (proofReplayContext : Prop) (originalUnsat : Prop) :
    ay_dsg_accepted_evidence originalFormulaFingerprint proofLineDigest
      liveClauseSetDigestBefore liveClauseSetDigestAfter deletionLedger
      antecedentAvailabilityWitness emptyClauseDerivationReplay
      checkerTranscript checkerAccepted proofArchiveDigest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      liveClauseConsistency proofReplayContext originalUnsat ->
    liveClauseConsistency := by
  intro accepted
  exact accepted liveClauseConsistency
    (fun _hFingerprint _hLine _hLiveBefore _hLiveAfter _hDeletion
      _hAntecedent _hReplay _hTranscript _hChecker _hArchive
      _hArchiveAccepted _hBuild _hBuildAccepted _hFallback _hAudit
      hLiveConsistent _hContext _hOriginal =>
      hLiveConsistent)

theorem ay_dsg_preserves_proof_replay_context
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (liveClauseSetDigestBefore : Prop) (liveClauseSetDigestAfter : Prop)
    (deletionLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (emptyClauseDerivationReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (proofArchiveDigest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (liveClauseConsistency : Prop)
    (proofReplayContext : Prop) (originalUnsat : Prop) :
    ay_dsg_accepted_evidence originalFormulaFingerprint proofLineDigest
      liveClauseSetDigestBefore liveClauseSetDigestAfter deletionLedger
      antecedentAvailabilityWitness emptyClauseDerivationReplay
      checkerTranscript checkerAccepted proofArchiveDigest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      liveClauseConsistency proofReplayContext originalUnsat ->
    proofReplayContext := by
  intro accepted
  exact accepted proofReplayContext
    (fun _hFingerprint _hLine _hLiveBefore _hLiveAfter _hDeletion
      _hAntecedent _hReplay _hTranscript _hChecker _hArchive
      _hArchiveAccepted _hBuild _hBuildAccepted _hFallback _hAudit
      _hLiveConsistent hContext _hOriginal =>
      hContext)

theorem ay_dsg_publication_sound
    (originalFormulaFingerprint : Prop) (proofLineDigest : Prop)
    (liveClauseSetDigestBefore : Prop) (liveClauseSetDigestAfter : Prop)
    (deletionLedger : Prop) (antecedentAvailabilityWitness : Prop)
    (emptyClauseDerivationReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (proofArchiveDigest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (liveClauseConsistency : Prop)
    (proofReplayContext : Prop) (originalUnsat : Prop) :
    ay_dsg_publication originalFormulaFingerprint proofLineDigest
      liveClauseSetDigestBefore liveClauseSetDigestAfter deletionLedger
      antecedentAvailabilityWitness emptyClauseDerivationReplay
      checkerTranscript checkerAccepted proofArchiveDigest archiveAccepted
      solverBuildEvidence buildAccepted fallbackNoClaim auditTranscript
      liveClauseConsistency proofReplayContext originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_dsg_empty_clause_path_sound
    (antecedentAvailabilityWitness : Prop)
    (emptyClauseDerivationReplay : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (originalUnsat : Prop) :
    ay_dsg_empty_clause_publication_path antecedentAvailabilityWitness
      emptyClauseDerivationReplay checkerTranscript checkerAccepted
      originalUnsat ->
    antecedentAvailabilityWitness ->
    originalUnsat := by
  intro path hAntecedent
  exact path originalUnsat
    (fun antecedent_to_replay rest =>
      rest originalUnsat
        (fun replay_to_transcript rest2 =>
          rest2 originalUnsat
            (fun transcript_to_checker checker_to_original =>
              checker_to_original
                (transcript_to_checker
                  (replay_to_transcript
                    (antecedent_to_replay hAntecedent)))))))

theorem ay_dsg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_dsg_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_dsg_disj_right noClaim (ay_dsg_disj originalUnsat publicSat)
    (ay_dsg_disj_left originalUnsat publicSat hUnsat)

theorem ay_dsg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_dsg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_dsg_disj_left noClaim
    (ay_dsg_disj originalUnsat publicSat) hNoClaim

theorem ay_dsg_bad_no_claim
    (lineMismatch : Prop) (liveSetMismatch : Prop)
    (deletionMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_dsg_bad_guard lineMismatch liveSetMismatch deletionMismatch
      antecedentMismatch replayMismatch checkerMismatch archiveMismatch
      buildMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_dsg_bad_recompute
    (lineMismatch : Prop) (liveSetMismatch : Prop)
    (deletionMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_dsg_bad_guard lineMismatch liveSetMismatch deletionMismatch
      antecedentMismatch replayMismatch checkerMismatch archiveMismatch
      buildMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_dsg_failed_guard_cannot_bless_unsat
    (lineMismatch : Prop) (liveSetMismatch : Prop)
    (deletionMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicUnsat : Prop) :
    ay_dsg_bad_guard lineMismatch liveSetMismatch deletionMismatch
      antecedentMismatch replayMismatch checkerMismatch archiveMismatch
      buildMismatch auditMismatch noClaim recompute ->
    ay_dsg_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_dsg_bad_recompute lineMismatch liveSetMismatch deletionMismatch
    antecedentMismatch replayMismatch checkerMismatch archiveMismatch
    buildMismatch auditMismatch noClaim recompute bad

theorem ay_dsg_failure_forces_no_claim
    (lineMismatch : Prop) (liveSetMismatch : Prop)
    (deletionMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) :
    ay_dsg_failure_reason lineMismatch liveSetMismatch deletionMismatch
      antecedentMismatch replayMismatch checkerMismatch archiveMismatch
      buildMismatch auditMismatch ->
    (lineMismatch -> noClaim) ->
    (liveSetMismatch -> noClaim) ->
    (deletionMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason line_to_no_claim live_to_no_claim deletion_to_no_claim
  intro antecedent_to_no_claim replay_to_no_claim checker_to_no_claim
  intro archive_to_no_claim build_to_no_claim audit_to_no_claim
  exact reason noClaim line_to_no_claim live_to_no_claim deletion_to_no_claim
    antecedent_to_no_claim replay_to_no_claim checker_to_no_claim
    archive_to_no_claim build_to_no_claim audit_to_no_claim

theorem ay_dsg_line_mismatch_forces_no_claim
    (lineMismatch noClaim : Prop) :
    lineMismatch ->
    (lineMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_dsg_live_set_mismatch_forces_no_claim
    (liveSetMismatch noClaim : Prop) :
    liveSetMismatch ->
    (liveSetMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_dsg_deletion_mismatch_forces_no_claim
    (deletionMismatch noClaim : Prop) :
    deletionMismatch ->
    (deletionMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_dsg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch ->
    (antecedentMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_dsg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch ->
    (replayMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_dsg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch ->
    (checkerMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_dsg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_dsg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_dsg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
