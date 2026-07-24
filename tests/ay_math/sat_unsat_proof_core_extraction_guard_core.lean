-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- UNSAT-core extraction guard soundness for ay sequential-main SAT-COMP
-- publication. Propositions stand for original formula digests, proof digests,
-- core-clause ledgers, input-clause origin maps, projection witnesses, proof
-- replay, empty-clause reachability witnesses, checker transcripts, benchmark
-- fingerprints, build/archive evidence, fallback no-claim paths, audit
-- transcripts, and fail-closed recompute diagnostics.

def ay_uceg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_uceg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_uceg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_uceg_accepted_evidence
    (originalFormulaDigest : Prop) (proofDigest : Prop)
    (coreClauseLedger : Prop) (inputClauseOriginMap : Prop)
    (projectionWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundCore : Prop) :=
  forall result : Prop,
    (originalFormulaDigest ->
      proofDigest ->
      coreClauseLedger ->
      inputClauseOriginMap ->
      projectionWitness ->
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
      soundCore ->
      result) ->
    result

def ay_uceg_core_projection_composition
    (originalFormulaDigest : Prop) (proofDigest : Prop)
    (coreClauseLedger : Prop) (inputClauseOriginMap : Prop)
    (projectionWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop)
    (soundCore : Prop) :=
  ay_uceg_conj
    (ay_uceg_conj
      (ay_uceg_map originalFormulaDigest proofDigest)
      (ay_uceg_conj
        (ay_uceg_map proofDigest coreClauseLedger)
        (ay_uceg_conj
          (ay_uceg_map coreClauseLedger inputClauseOriginMap)
          (ay_uceg_conj
            (ay_uceg_map inputClauseOriginMap projectionWitness)
            (ay_uceg_conj
              (ay_uceg_map projectionWitness proofReplay)
              (ay_uceg_conj
                (ay_uceg_map proofReplay emptyClauseReachabilityWitness)
                (ay_uceg_map emptyClauseReachabilityWitness
                  originalUnsat)))))))
    soundCore

def ay_uceg_publication
    (originalFormulaDigest : Prop) (proofDigest : Prop)
    (coreClauseLedger : Prop) (inputClauseOriginMap : Prop)
    (projectionWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundCore : Prop) :=
  ay_uceg_conj
    (ay_uceg_accepted_evidence originalFormulaDigest proofDigest
      coreClauseLedger inputClauseOriginMap projectionWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat soundCore)
    (ay_uceg_conj originalUnsat soundCore)

def ay_uceg_failure_reason
    (coreMismatch : Prop) (originMismatch : Prop)
    (projectionMismatch : Prop) (proofMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (coreMismatch -> result) ->
    (originMismatch -> result) ->
    (projectionMismatch -> result) ->
    (proofMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_uceg_bad_guard
    (coreMismatch : Prop) (originMismatch : Prop)
    (projectionMismatch : Prop) (proofMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_uceg_conj
    (ay_uceg_conj noClaim recompute)
    (ay_uceg_failure_reason coreMismatch originMismatch projectionMismatch
      proofMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch)

def ay_uceg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_uceg_disj noClaim (ay_uceg_disj originalUnsat publicSat)

theorem ay_uceg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_uceg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_uceg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_uceg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_uceg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_uceg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_uceg_build_accepted_evidence
    (originalFormulaDigest : Prop) (proofDigest : Prop)
    (coreClauseLedger : Prop) (inputClauseOriginMap : Prop)
    (projectionWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundCore : Prop) :
    originalFormulaDigest ->
    proofDigest ->
    coreClauseLedger ->
    inputClauseOriginMap ->
    projectionWitness ->
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
    soundCore ->
    ay_uceg_accepted_evidence originalFormulaDigest proofDigest
      coreClauseLedger inputClauseOriginMap projectionWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat soundCore := by
  intro hOriginalDigest hProof hCore hOrigin hProjection hReplay hEmpty
  intro hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
  intro hBuildAccepted hArchive hFallback hAudit hUnsat hCoreSound result publish
  exact publish hOriginalDigest hProof hCore hOrigin hProjection hReplay
    hEmpty hTranscript hChecker hFingerprint hFingerprintAccepted hBuild
    hBuildAccepted hArchive hFallback hAudit hUnsat hCoreSound

theorem ay_uceg_empty_clause_reachable
    (originalFormulaDigest : Prop) (proofDigest : Prop)
    (coreClauseLedger : Prop) (inputClauseOriginMap : Prop)
    (projectionWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundCore : Prop) :
    ay_uceg_accepted_evidence originalFormulaDigest proofDigest
      coreClauseLedger inputClauseOriginMap projectionWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat soundCore ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hOriginalDigest _hProof _hCore _hOrigin _hProjection _hReplay
      hEmpty _hTranscript _hChecker _hFingerprint _hFingerprintAccepted
      _hBuild _hBuildAccepted _hArchive _hFallback _hAudit _hUnsat
      _hCoreSound =>
      hEmpty)

theorem ay_uceg_original_unsat
    (originalFormulaDigest : Prop) (proofDigest : Prop)
    (coreClauseLedger : Prop) (inputClauseOriginMap : Prop)
    (projectionWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundCore : Prop) :
    ay_uceg_accepted_evidence originalFormulaDigest proofDigest
      coreClauseLedger inputClauseOriginMap projectionWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat soundCore ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hOriginalDigest _hProof _hCore _hOrigin _hProjection _hReplay
      _hEmpty _hTranscript _hChecker _hFingerprint _hFingerprintAccepted
      _hBuild _hBuildAccepted _hArchive _hFallback _hAudit hUnsat
      _hCoreSound =>
      hUnsat)

theorem ay_uceg_sound_core
    (originalFormulaDigest : Prop) (proofDigest : Prop)
    (coreClauseLedger : Prop) (inputClauseOriginMap : Prop)
    (projectionWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundCore : Prop) :
    ay_uceg_accepted_evidence originalFormulaDigest proofDigest
      coreClauseLedger inputClauseOriginMap projectionWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat soundCore ->
    soundCore := by
  intro accepted
  exact accepted soundCore
    (fun _hOriginalDigest _hProof _hCore _hOrigin _hProjection _hReplay
      _hEmpty _hTranscript _hChecker _hFingerprint _hFingerprintAccepted
      _hBuild _hBuildAccepted _hArchive _hFallback _hAudit _hUnsat
      hCoreSound =>
      hCoreSound)

theorem ay_uceg_core_projection_composes_to_original
    (originalFormulaDigest : Prop) (proofDigest : Prop)
    (coreClauseLedger : Prop) (inputClauseOriginMap : Prop)
    (projectionWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop)
    (soundCore : Prop) :
    ay_uceg_core_projection_composition originalFormulaDigest proofDigest
      coreClauseLedger inputClauseOriginMap projectionWitness proofReplay
      emptyClauseReachabilityWitness originalUnsat soundCore ->
    originalFormulaDigest ->
    ay_uceg_conj originalUnsat soundCore := by
  intro composition hOriginal
  exact composition (ay_uceg_conj originalUnsat soundCore)
    (fun chain hCoreSound =>
      ay_uceg_conj_intro originalUnsat soundCore
        (chain originalUnsat
          (fun original_to_proof rest =>
            rest originalUnsat
              (fun proof_to_core rest2 =>
                rest2 originalUnsat
                  (fun core_to_origin rest3 =>
                    rest3 originalUnsat
                      (fun origin_to_projection rest4 =>
                        rest4 originalUnsat
                          (fun projection_to_replay rest5 =>
                            rest5 originalUnsat
                              (fun replay_to_empty empty_to_unsat =>
                                empty_to_unsat
                                  (replay_to_empty
                                    (projection_to_replay
                                      (origin_to_projection
                                        (core_to_origin
                                          (proof_to_core
                                            (original_to_proof
                                              hOriginal)))))))))))))
        hCoreSound)

theorem ay_uceg_publication_sound
    (originalFormulaDigest : Prop) (proofDigest : Prop)
    (coreClauseLedger : Prop) (inputClauseOriginMap : Prop)
    (projectionWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundCore : Prop) :
    ay_uceg_publication originalFormulaDigest proofDigest coreClauseLedger
      inputClauseOriginMap projectionWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat soundCore ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted unsatAndCore =>
      unsatAndCore originalUnsat (fun hUnsat _hCore => hUnsat))

theorem ay_uceg_public_core_sound
    (originalFormulaDigest : Prop) (proofDigest : Prop)
    (coreClauseLedger : Prop) (inputClauseOriginMap : Prop)
    (projectionWitness : Prop) (proofReplay : Prop)
    (emptyClauseReachabilityWitness : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundCore : Prop) :
    ay_uceg_publication originalFormulaDigest proofDigest coreClauseLedger
      inputClauseOriginMap projectionWitness proofReplay
      emptyClauseReachabilityWitness checkerTranscript checkerAccepted
      benchmarkFingerprint fingerprintAccepted solverBuildEvidence
      buildAccepted archiveManifest fallbackNoClaim auditTranscript
      originalUnsat soundCore ->
    soundCore := by
  intro publication
  exact publication soundCore
    (fun _accepted unsatAndCore =>
      unsatAndCore soundCore (fun _hUnsat hCore => hCore))

theorem ay_uceg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_uceg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_uceg_disj_right noClaim (ay_uceg_disj originalUnsat publicSat)
    (ay_uceg_disj_left originalUnsat publicSat hOriginal)

theorem ay_uceg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_uceg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_uceg_disj_left noClaim (ay_uceg_disj originalUnsat publicSat)
    hNoClaim

theorem ay_uceg_bad_no_claim
    (coreMismatch : Prop) (originMismatch : Prop)
    (projectionMismatch : Prop) (proofMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uceg_bad_guard coreMismatch originMismatch projectionMismatch
      proofMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_uceg_bad_recompute
    (coreMismatch : Prop) (originMismatch : Prop)
    (projectionMismatch : Prop) (proofMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uceg_bad_guard coreMismatch originMismatch projectionMismatch
      proofMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_uceg_failed_guard_cannot_bless_unsat
    (coreMismatch : Prop) (originMismatch : Prop)
    (projectionMismatch : Prop) (proofMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_uceg_bad_guard coreMismatch originMismatch projectionMismatch
      proofMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    ay_uceg_disj noClaim originalUnsat := by
  intro bad
  exact ay_uceg_disj_left noClaim originalUnsat
    (ay_uceg_bad_no_claim coreMismatch originMismatch projectionMismatch
      proofMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_uceg_failed_guard_cannot_create_public_sat
    (coreMismatch : Prop) (originMismatch : Prop)
    (projectionMismatch : Prop) (proofMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_uceg_bad_guard coreMismatch originMismatch projectionMismatch
      proofMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute ->
    ay_uceg_disj noClaim publicSat := by
  intro bad
  exact ay_uceg_disj_left noClaim publicSat
    (ay_uceg_bad_no_claim coreMismatch originMismatch projectionMismatch
      proofMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_uceg_failure_forces_no_claim
    (coreMismatch : Prop) (originMismatch : Prop)
    (projectionMismatch : Prop) (proofMismatch : Prop)
    (replayMismatch : Prop) (checkerMismatch : Prop)
    (fingerprintMismatch : Prop) (buildMismatch : Prop)
    (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_uceg_failure_reason coreMismatch originMismatch projectionMismatch
      proofMismatch replayMismatch checkerMismatch fingerprintMismatch
      buildMismatch archiveMismatch auditMismatch ->
    (coreMismatch -> noClaim) ->
    (originMismatch -> noClaim) ->
    (projectionMismatch -> noClaim) ->
    (proofMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure core_to_no_claim origin_to_no_claim projection_to_no_claim
  intro proof_to_no_claim replay_to_no_claim checker_to_no_claim
  intro fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
  intro audit_to_no_claim
  exact failure noClaim core_to_no_claim origin_to_no_claim
    projection_to_no_claim proof_to_no_claim replay_to_no_claim
    checker_to_no_claim fingerprint_to_no_claim build_to_no_claim
    archive_to_no_claim audit_to_no_claim

theorem ay_uceg_core_mismatch_forces_no_claim
    (coreMismatch noClaim : Prop) :
    coreMismatch -> (coreMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uceg_origin_mismatch_forces_no_claim
    (originMismatch noClaim : Prop) :
    originMismatch -> (originMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uceg_projection_mismatch_forces_no_claim
    (projectionMismatch noClaim : Prop) :
    projectionMismatch -> (projectionMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uceg_proof_mismatch_forces_no_claim
    (proofMismatch noClaim : Prop) :
    proofMismatch -> (proofMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uceg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uceg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uceg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uceg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uceg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_uceg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
