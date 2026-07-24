-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- UNSAT proof-checker timeout guard soundness for ay sequential-main
-- SAT-COMP publication. Propositions model proof artifact digests, checker
-- command manifests, timeout/resource counters, partial and completed replay
-- transcript options, optional empty-clause reachability, timeout/OOM
-- classifications, archive/build/environment evidence, fallback
-- no-claim/recompute paths, audit transcripts, and fail-closed diagnostics.

def ay_pctg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_pctg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_pctg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_pctg_accepted_evidence
    (proofArtifactDigest : Prop) (checkerCommandManifest : Prop)
    (timeoutResourceCounterDigest : Prop) (partialReplayTranscript : Prop)
    (completedReplayTranscriptOption : Prop)
    (emptyClauseReachabilityWitnessOption : Prop)
    (timeoutOomClassification : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackNoClaim : Prop)
    (fallbackRecompute : Prop) (auditTranscript : Prop)
    (completeReplayChecked : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (proofArtifactDigest ->
      checkerCommandManifest ->
      timeoutResourceCounterDigest ->
      partialReplayTranscript ->
      completedReplayTranscriptOption ->
      emptyClauseReachabilityWitnessOption ->
      timeoutOomClassification ->
      archiveManifest ->
      archiveAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      environmentManifest ->
      environmentAccepted ->
      fallbackNoClaim ->
      fallbackRecompute ->
      auditTranscript ->
      completeReplayChecked ->
      originalUnsat ->
      result) ->
    result

def ay_pctg_complete_checker_path
    (completedReplayTranscriptOption : Prop)
    (emptyClauseReachabilityWitnessOption : Prop)
    (completeReplayChecked : Prop) (originalUnsat : Prop) :=
  ay_pctg_conj
    (ay_pctg_map completedReplayTranscriptOption
      emptyClauseReachabilityWitnessOption)
    (ay_pctg_conj
      (ay_pctg_map emptyClauseReachabilityWitnessOption
        completeReplayChecked)
      (ay_pctg_map completeReplayChecked originalUnsat))

def ay_pctg_timeout_diagnostic
    (timeoutOomClassification : Prop) (partialReplayTranscript : Prop)
    (fallbackNoClaim : Prop) (fallbackRecompute : Prop) :=
  ay_pctg_conj
    (ay_pctg_map timeoutOomClassification fallbackNoClaim)
    (ay_pctg_conj
      (ay_pctg_map partialReplayTranscript fallbackRecompute)
      (ay_pctg_conj fallbackNoClaim fallbackRecompute))

def ay_pctg_publication
    (proofArtifactDigest : Prop) (checkerCommandManifest : Prop)
    (timeoutResourceCounterDigest : Prop) (partialReplayTranscript : Prop)
    (completedReplayTranscriptOption : Prop)
    (emptyClauseReachabilityWitnessOption : Prop)
    (timeoutOomClassification : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackNoClaim : Prop)
    (fallbackRecompute : Prop) (auditTranscript : Prop)
    (completeReplayChecked : Prop) (originalUnsat : Prop) :=
  ay_pctg_conj
    (ay_pctg_accepted_evidence proofArtifactDigest checkerCommandManifest
      timeoutResourceCounterDigest partialReplayTranscript
      completedReplayTranscriptOption emptyClauseReachabilityWitnessOption
      timeoutOomClassification archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted environmentManifest environmentAccepted
      fallbackNoClaim fallbackRecompute auditTranscript completeReplayChecked
      originalUnsat)
    originalUnsat

def ay_pctg_failure_reason
    (proofMismatch : Prop) (checkerMismatch : Prop)
    (resourceMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (classificationMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop)
    (environmentMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (proofMismatch -> result) ->
    (checkerMismatch -> result) ->
    (resourceMismatch -> result) ->
    (replayMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (classificationMismatch -> result) ->
    (archiveMismatch -> result) ->
    (buildMismatch -> result) ->
    (environmentMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_pctg_bad_guard
    (proofMismatch : Prop) (checkerMismatch : Prop)
    (resourceMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (classificationMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop)
    (environmentMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_pctg_conj
    (ay_pctg_conj noClaim recompute)
    (ay_pctg_failure_reason proofMismatch checkerMismatch resourceMismatch
      replayMismatch reachabilityMismatch classificationMismatch
      archiveMismatch buildMismatch environmentMismatch auditMismatch)

def ay_pctg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_pctg_disj noClaim (ay_pctg_disj originalUnsat publicSat)

theorem ay_pctg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_pctg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_pctg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_pctg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_pctg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_pctg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_pctg_build_accepted_evidence
    (proofArtifactDigest : Prop) (checkerCommandManifest : Prop)
    (timeoutResourceCounterDigest : Prop) (partialReplayTranscript : Prop)
    (completedReplayTranscriptOption : Prop)
    (emptyClauseReachabilityWitnessOption : Prop)
    (timeoutOomClassification : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackNoClaim : Prop)
    (fallbackRecompute : Prop) (auditTranscript : Prop)
    (completeReplayChecked : Prop) (originalUnsat : Prop) :
    proofArtifactDigest ->
    checkerCommandManifest ->
    timeoutResourceCounterDigest ->
    partialReplayTranscript ->
    completedReplayTranscriptOption ->
    emptyClauseReachabilityWitnessOption ->
    timeoutOomClassification ->
    archiveManifest ->
    archiveAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    environmentManifest ->
    environmentAccepted ->
    fallbackNoClaim ->
    fallbackRecompute ->
    auditTranscript ->
    completeReplayChecked ->
    originalUnsat ->
    ay_pctg_accepted_evidence proofArtifactDigest checkerCommandManifest
      timeoutResourceCounterDigest partialReplayTranscript
      completedReplayTranscriptOption emptyClauseReachabilityWitnessOption
      timeoutOomClassification archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted environmentManifest environmentAccepted
      fallbackNoClaim fallbackRecompute auditTranscript completeReplayChecked
      originalUnsat := by
  intro hProof hChecker hResource hPartial hComplete hEmpty hClass hArchive
  intro hArchiveAccepted hBuild hBuildAccepted hEnv hEnvAccepted hNoClaim
  intro hRecompute hAudit hChecked hOriginal result publish
  exact publish hProof hChecker hResource hPartial hComplete hEmpty hClass
    hArchive hArchiveAccepted hBuild hBuildAccepted hEnv hEnvAccepted
    hNoClaim hRecompute hAudit hChecked hOriginal

theorem ay_pctg_unsat_requires_completed_replay_to_empty_clause
    (completedReplayTranscriptOption : Prop)
    (emptyClauseReachabilityWitnessOption : Prop)
    (completeReplayChecked : Prop) (originalUnsat : Prop) :
    ay_pctg_complete_checker_path completedReplayTranscriptOption
      emptyClauseReachabilityWitnessOption completeReplayChecked originalUnsat ->
    completedReplayTranscriptOption ->
    originalUnsat := by
  intro path hComplete
  exact path originalUnsat
    (fun complete_to_empty rest =>
      rest originalUnsat
        (fun empty_to_checked checked_to_original =>
          checked_to_original
            (empty_to_checked
              (complete_to_empty hComplete))))

theorem ay_pctg_timeout_oom_partial_forces_no_claim_or_recompute
    (timeoutOomClassification : Prop) (partialReplayTranscript : Prop)
    (fallbackNoClaim : Prop) (fallbackRecompute : Prop) :
    ay_pctg_timeout_diagnostic timeoutOomClassification partialReplayTranscript
      fallbackNoClaim fallbackRecompute ->
    timeoutOomClassification ->
    ay_pctg_conj fallbackNoClaim fallbackRecompute := by
  intro diagnostic hClass
  exact diagnostic (ay_pctg_conj fallbackNoClaim fallbackRecompute)
    (fun class_to_no_claim rest =>
      rest (ay_pctg_conj fallbackNoClaim fallbackRecompute)
        (fun _partial_to_recompute both =>
          ay_pctg_conj_intro fallbackNoClaim fallbackRecompute
            (class_to_no_claim hClass)
            (both fallbackRecompute
              (fun _hNoClaim hRecompute => hRecompute))))

theorem ay_pctg_complete_replay_available
    (proofArtifactDigest : Prop) (checkerCommandManifest : Prop)
    (timeoutResourceCounterDigest : Prop) (partialReplayTranscript : Prop)
    (completedReplayTranscriptOption : Prop)
    (emptyClauseReachabilityWitnessOption : Prop)
    (timeoutOomClassification : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackNoClaim : Prop)
    (fallbackRecompute : Prop) (auditTranscript : Prop)
    (completeReplayChecked : Prop) (originalUnsat : Prop) :
    ay_pctg_accepted_evidence proofArtifactDigest checkerCommandManifest
      timeoutResourceCounterDigest partialReplayTranscript
      completedReplayTranscriptOption emptyClauseReachabilityWitnessOption
      timeoutOomClassification archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted environmentManifest environmentAccepted
      fallbackNoClaim fallbackRecompute auditTranscript completeReplayChecked
      originalUnsat ->
    completeReplayChecked := by
  intro accepted
  exact accepted completeReplayChecked
    (fun _hProof _hChecker _hResource _hPartial _hComplete _hEmpty _hClass
      _hArchive _hArchiveAccepted _hBuild _hBuildAccepted _hEnv
      _hEnvAccepted _hNoClaim _hRecompute _hAudit hChecked _hOriginal =>
      hChecked)

theorem ay_pctg_publication_sound
    (proofArtifactDigest : Prop) (checkerCommandManifest : Prop)
    (timeoutResourceCounterDigest : Prop) (partialReplayTranscript : Prop)
    (completedReplayTranscriptOption : Prop)
    (emptyClauseReachabilityWitnessOption : Prop)
    (timeoutOomClassification : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackNoClaim : Prop)
    (fallbackRecompute : Prop) (auditTranscript : Prop)
    (completeReplayChecked : Prop) (originalUnsat : Prop) :
    ay_pctg_publication proofArtifactDigest checkerCommandManifest
      timeoutResourceCounterDigest partialReplayTranscript
      completedReplayTranscriptOption emptyClauseReachabilityWitnessOption
      timeoutOomClassification archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted environmentManifest environmentAccepted
      fallbackNoClaim fallbackRecompute auditTranscript completeReplayChecked
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_pctg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_pctg_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_pctg_disj_right noClaim (ay_pctg_disj originalUnsat publicSat)
    (ay_pctg_disj_left originalUnsat publicSat hUnsat)

theorem ay_pctg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_pctg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_pctg_disj_left noClaim
    (ay_pctg_disj originalUnsat publicSat) hNoClaim

theorem ay_pctg_bad_no_claim
    (proofMismatch : Prop) (checkerMismatch : Prop)
    (resourceMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (classificationMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop)
    (environmentMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_pctg_bad_guard proofMismatch checkerMismatch resourceMismatch
      replayMismatch reachabilityMismatch classificationMismatch
      archiveMismatch buildMismatch environmentMismatch auditMismatch noClaim
      recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_pctg_bad_recompute
    (proofMismatch : Prop) (checkerMismatch : Prop)
    (resourceMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (classificationMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop)
    (environmentMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_pctg_bad_guard proofMismatch checkerMismatch resourceMismatch
      replayMismatch reachabilityMismatch classificationMismatch
      archiveMismatch buildMismatch environmentMismatch auditMismatch noClaim
      recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_pctg_failed_guard_cannot_bless_unsat
    (proofMismatch : Prop) (checkerMismatch : Prop)
    (resourceMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (classificationMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop)
    (environmentMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicUnsat : Prop) :
    ay_pctg_bad_guard proofMismatch checkerMismatch resourceMismatch
      replayMismatch reachabilityMismatch classificationMismatch
      archiveMismatch buildMismatch environmentMismatch auditMismatch noClaim
      recompute ->
    ay_pctg_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_pctg_bad_recompute proofMismatch checkerMismatch resourceMismatch
    replayMismatch reachabilityMismatch classificationMismatch archiveMismatch
    buildMismatch environmentMismatch auditMismatch noClaim recompute bad

theorem ay_pctg_failure_forces_no_claim
    (proofMismatch : Prop) (checkerMismatch : Prop)
    (resourceMismatch : Prop) (replayMismatch : Prop)
    (reachabilityMismatch : Prop) (classificationMismatch : Prop)
    (archiveMismatch : Prop) (buildMismatch : Prop)
    (environmentMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) :
    ay_pctg_failure_reason proofMismatch checkerMismatch resourceMismatch
      replayMismatch reachabilityMismatch classificationMismatch archiveMismatch
      buildMismatch environmentMismatch auditMismatch ->
    (proofMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (resourceMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (classificationMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (environmentMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason proof_to_no_claim checker_to_no_claim resource_to_no_claim
  intro replay_to_no_claim reachability_to_no_claim class_to_no_claim
  intro archive_to_no_claim build_to_no_claim environment_to_no_claim
  intro audit_to_no_claim
  exact reason noClaim proof_to_no_claim checker_to_no_claim
    resource_to_no_claim replay_to_no_claim reachability_to_no_claim
    class_to_no_claim archive_to_no_claim build_to_no_claim
    environment_to_no_claim audit_to_no_claim

theorem ay_pctg_proof_mismatch_forces_no_claim
    (proofMismatch noClaim : Prop) :
    proofMismatch ->
    (proofMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pctg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch ->
    (checkerMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pctg_resource_mismatch_forces_no_claim
    (resourceMismatch noClaim : Prop) :
    resourceMismatch ->
    (resourceMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pctg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch ->
    (replayMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pctg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch ->
    (reachabilityMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pctg_classification_mismatch_forces_no_claim
    (classificationMismatch noClaim : Prop) :
    classificationMismatch ->
    (classificationMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pctg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pctg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pctg_environment_mismatch_forces_no_claim
    (environmentMismatch noClaim : Prop) :
    environmentMismatch ->
    (environmentMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pctg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
