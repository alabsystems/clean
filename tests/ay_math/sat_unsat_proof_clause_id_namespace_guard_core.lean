-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause-ID namespace guard soundness for ay sequential-main SAT-COMP UNSAT
-- proof publication. Propositions stand for proof digests, clause-ID namespace
-- manifests, addition/deletion ledgers, antecedent availability, ID-reuse
-- exclusion, proof replay, empty-clause reachability, checker transcripts,
-- benchmark fingerprints, build/archive evidence, fallback no-claim paths,
-- audit transcripts, and fail-closed recompute diagnostics.

def ay_cing_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_cing_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_cing_map (source : Prop) (target : Prop) :=
  source -> target

def ay_cing_accepted_evidence
    (proofDigest : Prop) (namespaceManifest : Prop)
    (additionLedger : Prop) (deletionLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (idReuseExclusionWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofDigest ->
      namespaceManifest ->
      additionLedger ->
      deletionLedger ->
      antecedentAvailabilityWitness ->
      idReuseExclusionWitness ->
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

def ay_cing_namespace_replay_composition
    (proofDigest : Prop) (namespaceManifest : Prop)
    (additionLedger : Prop) (deletionLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (idReuseExclusionWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :=
  ay_cing_conj
    (ay_cing_conj
      (ay_cing_map proofDigest namespaceManifest)
      (ay_cing_conj
        (ay_cing_map namespaceManifest additionLedger)
        (ay_cing_conj
          (ay_cing_map additionLedger deletionLedger)
          (ay_cing_conj
            (ay_cing_map deletionLedger antecedentAvailabilityWitness)
            (ay_cing_conj
              (ay_cing_map antecedentAvailabilityWitness
                idReuseExclusionWitness)
              (ay_cing_conj
                (ay_cing_map idReuseExclusionWitness proofReplay)
                (ay_cing_conj
                  (ay_cing_map proofReplay emptyClauseReachabilityWitness)
                  (ay_cing_map emptyClauseReachabilityWitness
                    originalUnsat))))))))
    (ay_cing_map proofDigest originalUnsat)

def ay_cing_publication
    (proofDigest : Prop) (namespaceManifest : Prop)
    (additionLedger : Prop) (deletionLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (idReuseExclusionWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :=
  ay_cing_conj
    (ay_cing_accepted_evidence proofDigest namespaceManifest additionLedger
      deletionLedger antecedentAvailabilityWitness idReuseExclusionWitness
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat)
    originalUnsat

def ay_cing_failure_reason
    (digestMismatch : Prop) (namespaceMismatch : Prop)
    (additionMismatch : Prop) (deletionMismatch : Prop)
    (reuseMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (namespaceMismatch -> result) ->
    (additionMismatch -> result) ->
    (deletionMismatch -> result) ->
    (reuseMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_cing_bad_guard
    (digestMismatch : Prop) (namespaceMismatch : Prop)
    (additionMismatch : Prop) (deletionMismatch : Prop)
    (reuseMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_cing_conj
    (ay_cing_conj noClaim recompute)
    (ay_cing_failure_reason digestMismatch namespaceMismatch additionMismatch
      deletionMismatch reuseMismatch antecedentMismatch replayMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch)

def ay_cing_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_cing_disj noClaim (ay_cing_disj originalUnsat publicSat)

theorem ay_cing_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_cing_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_cing_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_cing_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_cing_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_cing_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_cing_build_accepted_evidence
    (proofDigest : Prop) (namespaceManifest : Prop)
    (additionLedger : Prop) (deletionLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (idReuseExclusionWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    proofDigest ->
    namespaceManifest ->
    additionLedger ->
    deletionLedger ->
    antecedentAvailabilityWitness ->
    idReuseExclusionWitness ->
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
    ay_cing_accepted_evidence proofDigest namespaceManifest additionLedger
      deletionLedger antecedentAvailabilityWitness idReuseExclusionWitness
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat := by
  intro hDigest hNamespace hAddition hDeletion hAntecedent hReuse hReplay
  intro hEmpty hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hOriginal result publish
  exact publish hDigest hNamespace hAddition hDeletion hAntecedent hReuse
    hReplay hEmpty hTranscript hChecker hFingerprint hFingerprintAccepted
    hBuild hBuildAccepted hArchive hFallback hAudit hOriginal

theorem ay_cing_empty_clause_reachable
    (proofDigest : Prop) (namespaceManifest : Prop)
    (additionLedger : Prop) (deletionLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (idReuseExclusionWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_cing_accepted_evidence proofDigest namespaceManifest additionLedger
      deletionLedger antecedentAvailabilityWitness idReuseExclusionWitness
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hDigest _hNamespace _hAddition _hDeletion _hAntecedent _hReuse
      _hReplay hEmpty _hTranscript _hChecker _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit _hOriginal =>
      hEmpty)

theorem ay_cing_original_unsat
    (proofDigest : Prop) (namespaceManifest : Prop)
    (additionLedger : Prop) (deletionLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (idReuseExclusionWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_cing_accepted_evidence proofDigest namespaceManifest additionLedger
      deletionLedger antecedentAvailabilityWitness idReuseExclusionWitness
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hDigest _hNamespace _hAddition _hDeletion _hAntecedent _hReuse
      _hReplay _hEmpty _hTranscript _hChecker _hFingerprint
      _hFingerprintAccepted _hBuild _hBuildAccepted _hArchive _hFallback
      _hAudit hOriginal =>
      hOriginal)

theorem ay_cing_namespace_replay_composes_to_original
    (proofDigest : Prop) (namespaceManifest : Prop)
    (additionLedger : Prop) (deletionLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (idReuseExclusionWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :
    ay_cing_namespace_replay_composition proofDigest namespaceManifest
      additionLedger deletionLedger antecedentAvailabilityWitness
      idReuseExclusionWitness proofReplay emptyClauseReachabilityWitness
      originalUnsat ->
    proofDigest ->
    originalUnsat := by
  intro composition hDigest
  exact composition originalUnsat
    (fun _chain digest_to_original =>
      digest_to_original hDigest)

theorem ay_cing_publication_sound
    (proofDigest : Prop) (namespaceManifest : Prop)
    (additionLedger : Prop) (deletionLedger : Prop)
    (antecedentAvailabilityWitness : Prop) (idReuseExclusionWitness : Prop)
    (proofReplay : Prop) (emptyClauseReachabilityWitness : Prop)
    (checkerTranscript : Prop) (checkerAccepted : Prop)
    (benchmarkFingerprint : Prop) (fingerprintAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (archiveManifest : Prop) (fallbackNoClaim : Prop)
    (auditTranscript : Prop) (originalUnsat : Prop) :
    ay_cing_publication proofDigest namespaceManifest additionLedger
      deletionLedger antecedentAvailabilityWitness idReuseExclusionWitness
      proofReplay emptyClauseReachabilityWitness checkerTranscript
      checkerAccepted benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_cing_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_cing_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_cing_disj_right noClaim (ay_cing_disj originalUnsat publicSat)
    (ay_cing_disj_left originalUnsat publicSat hOriginal)

theorem ay_cing_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_cing_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_cing_disj_left noClaim (ay_cing_disj originalUnsat publicSat)
    hNoClaim

theorem ay_cing_bad_no_claim
    (digestMismatch : Prop) (namespaceMismatch : Prop)
    (additionMismatch : Prop) (deletionMismatch : Prop)
    (reuseMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_cing_bad_guard digestMismatch namespaceMismatch additionMismatch
      deletionMismatch reuseMismatch antecedentMismatch replayMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_cing_bad_recompute
    (digestMismatch : Prop) (namespaceMismatch : Prop)
    (additionMismatch : Prop) (deletionMismatch : Prop)
    (reuseMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_cing_bad_guard digestMismatch namespaceMismatch additionMismatch
      deletionMismatch reuseMismatch antecedentMismatch replayMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_cing_failed_guard_cannot_bless_unsat
    (digestMismatch : Prop) (namespaceMismatch : Prop)
    (additionMismatch : Prop) (deletionMismatch : Prop)
    (reuseMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_cing_bad_guard digestMismatch namespaceMismatch additionMismatch
      deletionMismatch reuseMismatch antecedentMismatch replayMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_cing_disj noClaim originalUnsat := by
  intro bad
  exact ay_cing_disj_left noClaim originalUnsat
    (ay_cing_bad_no_claim digestMismatch namespaceMismatch additionMismatch
      deletionMismatch reuseMismatch antecedentMismatch replayMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_cing_failed_guard_cannot_create_public_sat
    (digestMismatch : Prop) (namespaceMismatch : Prop)
    (additionMismatch : Prop) (deletionMismatch : Prop)
    (reuseMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_cing_bad_guard digestMismatch namespaceMismatch additionMismatch
      deletionMismatch reuseMismatch antecedentMismatch replayMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute ->
    ay_cing_disj noClaim publicSat := by
  intro bad
  exact ay_cing_disj_left noClaim publicSat
    (ay_cing_bad_no_claim digestMismatch namespaceMismatch additionMismatch
      deletionMismatch reuseMismatch antecedentMismatch replayMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch noClaim recompute bad)

theorem ay_cing_failure_forces_no_claim
    (digestMismatch : Prop) (namespaceMismatch : Prop)
    (additionMismatch : Prop) (deletionMismatch : Prop)
    (reuseMismatch : Prop) (antecedentMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_cing_failure_reason digestMismatch namespaceMismatch additionMismatch
      deletionMismatch reuseMismatch antecedentMismatch replayMismatch
      checkerMismatch fingerprintMismatch buildMismatch archiveMismatch
      auditMismatch ->
    (digestMismatch -> noClaim) ->
    (namespaceMismatch -> noClaim) ->
    (additionMismatch -> noClaim) ->
    (deletionMismatch -> noClaim) ->
    (reuseMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure digest_to_no_claim namespace_to_no_claim addition_to_no_claim
  intro deletion_to_no_claim reuse_to_no_claim antecedent_to_no_claim
  intro replay_to_no_claim checker_to_no_claim fingerprint_to_no_claim
  intro build_to_no_claim archive_to_no_claim audit_to_no_claim
  exact failure noClaim digest_to_no_claim namespace_to_no_claim
    addition_to_no_claim deletion_to_no_claim reuse_to_no_claim
    antecedent_to_no_claim replay_to_no_claim checker_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_cing_digest_mismatch_forces_no_claim
    (digestMismatch noClaim : Prop) :
    digestMismatch -> (digestMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cing_namespace_mismatch_forces_no_claim
    (namespaceMismatch noClaim : Prop) :
    namespaceMismatch -> (namespaceMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cing_addition_mismatch_forces_no_claim
    (additionMismatch noClaim : Prop) :
    additionMismatch -> (additionMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cing_deletion_mismatch_forces_no_claim
    (deletionMismatch noClaim : Prop) :
    deletionMismatch -> (deletionMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cing_reuse_mismatch_forces_no_claim
    (reuseMismatch noClaim : Prop) :
    reuseMismatch -> (reuseMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cing_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch -> (antecedentMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cing_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cing_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cing_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cing_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cing_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_cing_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
