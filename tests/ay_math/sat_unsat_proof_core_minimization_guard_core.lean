-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- UNSAT-core minimization guard soundness for ay sequential-main SAT-COMP
-- publication. Propositions stand for original formula digests, source and
-- minimized core ledgers, removal witnesses, minimized-core replay/checker
-- evidence, empty-clause reachability witnesses, benchmark fingerprints,
-- build/archive evidence, fallback no-claim paths, audit transcripts, and
-- fail-closed recompute diagnostics.

def ay_ucmg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_ucmg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_ucmg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_ucmg_accepted_evidence
    (originalFormulaDigest : Prop) (sourceCoreLedger : Prop)
    (minimizedCoreLedger : Prop) (removalWitness : Prop)
    (minimizedCoreReplay : Prop) (checkerTranscript : Prop)
    (emptyClauseReachabilityWitness : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundMinimizedCore : Prop) :=
  forall result : Prop,
    (originalFormulaDigest ->
      sourceCoreLedger ->
      minimizedCoreLedger ->
      removalWitness ->
      minimizedCoreReplay ->
      checkerTranscript ->
      emptyClauseReachabilityWitness ->
      benchmarkFingerprint ->
      fingerprintAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      archiveManifest ->
      fallbackNoClaim ->
      auditTranscript ->
      originalUnsat ->
      soundMinimizedCore ->
      result) ->
    result

def ay_ucmg_minimized_core_composition
    (originalFormulaDigest : Prop) (sourceCoreLedger : Prop)
    (minimizedCoreLedger : Prop) (removalWitness : Prop)
    (minimizedCoreReplay : Prop) (checkerTranscript : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop)
    (soundMinimizedCore : Prop) :=
  ay_ucmg_conj
    (ay_ucmg_conj
      (ay_ucmg_map originalFormulaDigest sourceCoreLedger)
      (ay_ucmg_conj
        (ay_ucmg_map sourceCoreLedger minimizedCoreLedger)
        (ay_ucmg_conj
          (ay_ucmg_map minimizedCoreLedger removalWitness)
          (ay_ucmg_conj
            (ay_ucmg_map removalWitness minimizedCoreReplay)
            (ay_ucmg_conj
              (ay_ucmg_map minimizedCoreReplay checkerTranscript)
              (ay_ucmg_conj
                (ay_ucmg_map checkerTranscript emptyClauseReachabilityWitness)
                (ay_ucmg_map emptyClauseReachabilityWitness
                  originalUnsat)))))))
    soundMinimizedCore

def ay_ucmg_publication
    (originalFormulaDigest : Prop) (sourceCoreLedger : Prop)
    (minimizedCoreLedger : Prop) (removalWitness : Prop)
    (minimizedCoreReplay : Prop) (checkerTranscript : Prop)
    (emptyClauseReachabilityWitness : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundMinimizedCore : Prop) :=
  ay_ucmg_conj
    (ay_ucmg_accepted_evidence originalFormulaDigest sourceCoreLedger
      minimizedCoreLedger removalWitness minimizedCoreReplay checkerTranscript
      emptyClauseReachabilityWitness benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat soundMinimizedCore)
    (ay_ucmg_conj originalUnsat soundMinimizedCore)

def ay_ucmg_failure_reason
    (sourceMismatch : Prop) (minimizedMismatch : Prop)
    (removalMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (sourceMismatch -> result) ->
    (minimizedMismatch -> result) ->
    (removalMismatch -> result) ->
    (replayMismatch -> result) ->
    (checkerMismatch -> result) ->
    (fingerprintMismatch -> result) ->
    (buildMismatch -> result) ->
    (archiveMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_ucmg_bad_guard
    (sourceMismatch : Prop) (minimizedMismatch : Prop)
    (removalMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_ucmg_conj
    (ay_ucmg_conj noClaim recompute)
    (ay_ucmg_failure_reason sourceMismatch minimizedMismatch removalMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch)

def ay_ucmg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_ucmg_disj noClaim (ay_ucmg_disj originalUnsat publicSat)

theorem ay_ucmg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_ucmg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_ucmg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_ucmg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_ucmg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_ucmg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_ucmg_build_accepted_evidence
    (originalFormulaDigest : Prop) (sourceCoreLedger : Prop)
    (minimizedCoreLedger : Prop) (removalWitness : Prop)
    (minimizedCoreReplay : Prop) (checkerTranscript : Prop)
    (emptyClauseReachabilityWitness : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundMinimizedCore : Prop) :
    originalFormulaDigest ->
    sourceCoreLedger ->
    minimizedCoreLedger ->
    removalWitness ->
    minimizedCoreReplay ->
    checkerTranscript ->
    emptyClauseReachabilityWitness ->
    benchmarkFingerprint ->
    fingerprintAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    archiveManifest ->
    fallbackNoClaim ->
    auditTranscript ->
    originalUnsat ->
    soundMinimizedCore ->
    ay_ucmg_accepted_evidence originalFormulaDigest sourceCoreLedger
      minimizedCoreLedger removalWitness minimizedCoreReplay checkerTranscript
      emptyClauseReachabilityWitness benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat soundMinimizedCore := by
  intro hOriginal hSource hMinimized hRemoval hReplay hChecker hEmpty
  intro hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
  intro hFallback hAudit hUnsat hCore result publish
  exact publish hOriginal hSource hMinimized hRemoval hReplay hChecker hEmpty
    hFingerprint hFingerprintAccepted hBuild hBuildAccepted hArchive
    hFallback hAudit hUnsat hCore

theorem ay_ucmg_original_unsat
    (originalFormulaDigest : Prop) (sourceCoreLedger : Prop)
    (minimizedCoreLedger : Prop) (removalWitness : Prop)
    (minimizedCoreReplay : Prop) (checkerTranscript : Prop)
    (emptyClauseReachabilityWitness : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundMinimizedCore : Prop) :
    ay_ucmg_accepted_evidence originalFormulaDigest sourceCoreLedger
      minimizedCoreLedger removalWitness minimizedCoreReplay checkerTranscript
      emptyClauseReachabilityWitness benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat soundMinimizedCore ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat
    (fun _hOriginal _hSource _hMinimized _hRemoval _hReplay _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit hUnsat _hCore =>
      hUnsat)

theorem ay_ucmg_sound_minimized_core
    (originalFormulaDigest : Prop) (sourceCoreLedger : Prop)
    (minimizedCoreLedger : Prop) (removalWitness : Prop)
    (minimizedCoreReplay : Prop) (checkerTranscript : Prop)
    (emptyClauseReachabilityWitness : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundMinimizedCore : Prop) :
    ay_ucmg_accepted_evidence originalFormulaDigest sourceCoreLedger
      minimizedCoreLedger removalWitness minimizedCoreReplay checkerTranscript
      emptyClauseReachabilityWitness benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat soundMinimizedCore ->
    soundMinimizedCore := by
  intro accepted
  exact accepted soundMinimizedCore
    (fun _hOriginal _hSource _hMinimized _hRemoval _hReplay _hChecker
      _hEmpty _hFingerprint _hFingerprintAccepted _hBuild _hBuildAccepted
      _hArchive _hFallback _hAudit _hUnsat hCore =>
      hCore)

theorem ay_ucmg_minimized_core_composes_to_original
    (originalFormulaDigest : Prop) (sourceCoreLedger : Prop)
    (minimizedCoreLedger : Prop) (removalWitness : Prop)
    (minimizedCoreReplay : Prop) (checkerTranscript : Prop)
    (emptyClauseReachabilityWitness : Prop) (originalUnsat : Prop)
    (soundMinimizedCore : Prop) :
    ay_ucmg_minimized_core_composition originalFormulaDigest sourceCoreLedger
      minimizedCoreLedger removalWitness minimizedCoreReplay checkerTranscript
      emptyClauseReachabilityWitness originalUnsat soundMinimizedCore ->
    originalFormulaDigest ->
    ay_ucmg_conj originalUnsat soundMinimizedCore := by
  intro composition hOriginal
  exact composition (ay_ucmg_conj originalUnsat soundMinimizedCore)
    (fun chain hCore =>
      ay_ucmg_conj_intro originalUnsat soundMinimizedCore
        (chain originalUnsat
          (fun original_to_source rest =>
            rest originalUnsat
              (fun source_to_minimized rest2 =>
                rest2 originalUnsat
                  (fun minimized_to_removal rest3 =>
                    rest3 originalUnsat
                      (fun removal_to_replay rest4 =>
                        rest4 originalUnsat
                          (fun replay_to_checker rest5 =>
                            rest5 originalUnsat
                              (fun checker_to_empty empty_to_unsat =>
                                empty_to_unsat
                                  (checker_to_empty
                                    (replay_to_checker
                                      (removal_to_replay
                                        (minimized_to_removal
                                          (source_to_minimized
                                            (original_to_source
                                              hOriginal)))))))))))))
        hCore)

theorem ay_ucmg_publication_sound
    (originalFormulaDigest : Prop) (sourceCoreLedger : Prop)
    (minimizedCoreLedger : Prop) (removalWitness : Prop)
    (minimizedCoreReplay : Prop) (checkerTranscript : Prop)
    (emptyClauseReachabilityWitness : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundMinimizedCore : Prop) :
    ay_ucmg_publication originalFormulaDigest sourceCoreLedger
      minimizedCoreLedger removalWitness minimizedCoreReplay checkerTranscript
      emptyClauseReachabilityWitness benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat soundMinimizedCore ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted unsatAndCore =>
      unsatAndCore originalUnsat (fun hUnsat _hCore => hUnsat))

theorem ay_ucmg_public_core_sound
    (originalFormulaDigest : Prop) (sourceCoreLedger : Prop)
    (minimizedCoreLedger : Prop) (removalWitness : Prop)
    (minimizedCoreReplay : Prop) (checkerTranscript : Prop)
    (emptyClauseReachabilityWitness : Prop) (benchmarkFingerprint : Prop)
    (fingerprintAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (archiveManifest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (originalUnsat : Prop) (soundMinimizedCore : Prop) :
    ay_ucmg_publication originalFormulaDigest sourceCoreLedger
      minimizedCoreLedger removalWitness minimizedCoreReplay checkerTranscript
      emptyClauseReachabilityWitness benchmarkFingerprint fingerprintAccepted
      solverBuildEvidence buildAccepted archiveManifest fallbackNoClaim
      auditTranscript originalUnsat soundMinimizedCore ->
    soundMinimizedCore := by
  intro publication
  exact publication soundMinimizedCore
    (fun _accepted unsatAndCore =>
      unsatAndCore soundMinimizedCore (fun _hUnsat hCore => hCore))

theorem ay_ucmg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_ucmg_public_report noClaim originalUnsat publicSat := by
  intro hOriginal
  exact ay_ucmg_disj_right noClaim (ay_ucmg_disj originalUnsat publicSat)
    (ay_ucmg_disj_left originalUnsat publicSat hOriginal)

theorem ay_ucmg_bad_no_claim
    (sourceMismatch : Prop) (minimizedMismatch : Prop)
    (removalMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ucmg_bad_guard sourceMismatch minimizedMismatch removalMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute noClaim (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_ucmg_bad_recompute
    (sourceMismatch : Prop) (minimizedMismatch : Prop)
    (removalMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ucmg_bad_guard sourceMismatch minimizedMismatch removalMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun noClaimAndRecompute _failure =>
      noClaimAndRecompute recompute (fun _hNoClaim hRecompute => hRecompute))

theorem ay_ucmg_failed_guard_cannot_bless_unsat
    (sourceMismatch : Prop) (minimizedMismatch : Prop)
    (removalMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    ay_ucmg_bad_guard sourceMismatch minimizedMismatch removalMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_ucmg_disj noClaim originalUnsat := by
  intro bad
  exact ay_ucmg_disj_left noClaim originalUnsat
    (ay_ucmg_bad_no_claim sourceMismatch minimizedMismatch removalMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_ucmg_failed_guard_cannot_create_public_sat
    (sourceMismatch : Prop) (minimizedMismatch : Prop)
    (removalMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicSat : Prop) :
    ay_ucmg_bad_guard sourceMismatch minimizedMismatch removalMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute ->
    ay_ucmg_disj noClaim publicSat := by
  intro bad
  exact ay_ucmg_disj_left noClaim publicSat
    (ay_ucmg_bad_no_claim sourceMismatch minimizedMismatch removalMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch noClaim recompute bad)

theorem ay_ucmg_failure_forces_no_claim
    (sourceMismatch : Prop) (minimizedMismatch : Prop)
    (removalMismatch : Prop) (replayMismatch : Prop)
    (checkerMismatch : Prop) (fingerprintMismatch : Prop)
    (buildMismatch : Prop) (archiveMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ucmg_failure_reason sourceMismatch minimizedMismatch removalMismatch
      replayMismatch checkerMismatch fingerprintMismatch buildMismatch
      archiveMismatch auditMismatch ->
    (sourceMismatch -> noClaim) ->
    (minimizedMismatch -> noClaim) ->
    (removalMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (fingerprintMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro failure source_to_no_claim minimized_to_no_claim removal_to_no_claim
  intro replay_to_no_claim checker_to_no_claim fingerprint_to_no_claim
  intro build_to_no_claim archive_to_no_claim audit_to_no_claim
  exact failure noClaim source_to_no_claim minimized_to_no_claim
    removal_to_no_claim replay_to_no_claim checker_to_no_claim
    fingerprint_to_no_claim build_to_no_claim archive_to_no_claim
    audit_to_no_claim

theorem ay_ucmg_source_mismatch_forces_no_claim
    (sourceMismatch noClaim : Prop) :
    sourceMismatch -> (sourceMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ucmg_minimized_mismatch_forces_no_claim
    (minimizedMismatch noClaim : Prop) :
    minimizedMismatch -> (minimizedMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ucmg_removal_mismatch_forces_no_claim
    (removalMismatch noClaim : Prop) :
    removalMismatch -> (removalMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ucmg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch -> (replayMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ucmg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch -> (checkerMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ucmg_fingerprint_mismatch_forces_no_claim
    (fingerprintMismatch noClaim : Prop) :
    fingerprintMismatch -> (fingerprintMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ucmg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch -> (buildMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ucmg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch -> (archiveMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch

theorem ay_ucmg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch -> (auditMismatch -> noClaim) -> noClaim := by
  intro mismatch close
  exact close mismatch
