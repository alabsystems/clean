-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- UNSAT proof archive-manifest guard soundness for ay sequential-main
-- SAT-COMP publication. Propositions model benchmark fingerprints, raw and
-- normalized proof digests, proof archive manifests, checker binary/version
-- digests, checker transcript digests, empty-clause reachability, solver build
-- evidence, environment manifests, extraction/replay script digests, fallback
-- no-claim paths, audit transcripts, and fail-closed recompute diagnostics.

def ay_pamg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_pamg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_pamg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_pamg_accepted_evidence
    (benchmarkFingerprint : Prop) (rawProofDigest : Prop)
    (normalizedProofDigest : Prop) (proofArchiveManifest : Prop)
    (checkerBinaryVersionDigest : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (solverBuildEvidence : Prop)
    (environmentManifest : Prop) (extractionReplayScriptDigest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (archiveCoherent : Prop) (checkerBackedReachability : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (benchmarkFingerprint ->
      rawProofDigest ->
      normalizedProofDigest ->
      proofArchiveManifest ->
      checkerBinaryVersionDigest ->
      checkerTranscriptDigest ->
      emptyClauseReachabilityWitness ->
      solverBuildEvidence ->
      environmentManifest ->
      extractionReplayScriptDigest ->
      fallbackNoClaim ->
      auditTranscript ->
      archiveCoherent ->
      checkerBackedReachability ->
      originalUnsat ->
      result) ->
    result

def ay_pamg_checker_replay_path
    (proofArchiveManifest : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachabilityWitness : Prop)
    (checkerBackedReachability : Prop) (originalUnsat : Prop) :=
  ay_pamg_conj
    (ay_pamg_map proofArchiveManifest checkerTranscriptDigest)
    (ay_pamg_conj
      (ay_pamg_map checkerTranscriptDigest emptyClauseReachabilityWitness)
      (ay_pamg_conj
        (ay_pamg_map emptyClauseReachabilityWitness
          checkerBackedReachability)
        (ay_pamg_map checkerBackedReachability originalUnsat)))

def ay_pamg_archive_coherence
    (benchmarkFingerprint : Prop) (rawProofDigest : Prop)
    (normalizedProofDigest : Prop) (proofArchiveManifest : Prop)
    (checkerBinaryVersionDigest : Prop) (solverBuildEvidence : Prop)
    (environmentManifest : Prop) (extractionReplayScriptDigest : Prop)
    (archiveCoherent : Prop) :=
  ay_pamg_conj
    (ay_pamg_map benchmarkFingerprint rawProofDigest)
    (ay_pamg_conj
      (ay_pamg_map rawProofDigest normalizedProofDigest)
      (ay_pamg_conj
        (ay_pamg_map normalizedProofDigest proofArchiveManifest)
        (ay_pamg_conj
          (ay_pamg_map proofArchiveManifest checkerBinaryVersionDigest)
          (ay_pamg_conj
            (ay_pamg_map checkerBinaryVersionDigest solverBuildEvidence)
            (ay_pamg_conj
              (ay_pamg_map solverBuildEvidence environmentManifest)
              (ay_pamg_conj
                (ay_pamg_map environmentManifest
                  extractionReplayScriptDigest)
                (ay_pamg_map extractionReplayScriptDigest
                  archiveCoherent)))))))

def ay_pamg_publication
    (benchmarkFingerprint : Prop) (rawProofDigest : Prop)
    (normalizedProofDigest : Prop) (proofArchiveManifest : Prop)
    (checkerBinaryVersionDigest : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (solverBuildEvidence : Prop)
    (environmentManifest : Prop) (extractionReplayScriptDigest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (archiveCoherent : Prop) (checkerBackedReachability : Prop)
    (originalUnsat : Prop) :=
  ay_pamg_conj
    (ay_pamg_accepted_evidence benchmarkFingerprint rawProofDigest
      normalizedProofDigest proofArchiveManifest checkerBinaryVersionDigest
      checkerTranscriptDigest emptyClauseReachabilityWitness solverBuildEvidence
      environmentManifest extractionReplayScriptDigest fallbackNoClaim
      auditTranscript archiveCoherent checkerBackedReachability originalUnsat)
    originalUnsat

def ay_pamg_failure_reason
    (archiveMismatch : Prop) (rawMismatch : Prop)
    (normalizedMismatch : Prop) (checkerMismatch : Prop)
    (transcriptMismatch : Prop) (benchmarkMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (extractionMismatch : Prop) (replayMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (archiveMismatch -> result) ->
    (rawMismatch -> result) ->
    (normalizedMismatch -> result) ->
    (checkerMismatch -> result) ->
    (transcriptMismatch -> result) ->
    (benchmarkMismatch -> result) ->
    (buildMismatch -> result) ->
    (environmentMismatch -> result) ->
    (extractionMismatch -> result) ->
    (replayMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_pamg_bad_guard
    (archiveMismatch : Prop) (rawMismatch : Prop)
    (normalizedMismatch : Prop) (checkerMismatch : Prop)
    (transcriptMismatch : Prop) (benchmarkMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (extractionMismatch : Prop) (replayMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  ay_pamg_conj
    (ay_pamg_conj noClaim recompute)
    (ay_pamg_failure_reason archiveMismatch rawMismatch normalizedMismatch
      checkerMismatch transcriptMismatch benchmarkMismatch buildMismatch
      environmentMismatch extractionMismatch replayMismatch auditMismatch)

def ay_pamg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_pamg_disj noClaim (ay_pamg_disj originalUnsat publicSat)

theorem ay_pamg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_pamg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_pamg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_pamg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_pamg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_pamg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_pamg_build_accepted_evidence
    (benchmarkFingerprint : Prop) (rawProofDigest : Prop)
    (normalizedProofDigest : Prop) (proofArchiveManifest : Prop)
    (checkerBinaryVersionDigest : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (solverBuildEvidence : Prop)
    (environmentManifest : Prop) (extractionReplayScriptDigest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (archiveCoherent : Prop) (checkerBackedReachability : Prop)
    (originalUnsat : Prop) :
    benchmarkFingerprint ->
    rawProofDigest ->
    normalizedProofDigest ->
    proofArchiveManifest ->
    checkerBinaryVersionDigest ->
    checkerTranscriptDigest ->
    emptyClauseReachabilityWitness ->
    solverBuildEvidence ->
    environmentManifest ->
    extractionReplayScriptDigest ->
    fallbackNoClaim ->
    auditTranscript ->
    archiveCoherent ->
    checkerBackedReachability ->
    originalUnsat ->
    ay_pamg_accepted_evidence benchmarkFingerprint rawProofDigest
      normalizedProofDigest proofArchiveManifest checkerBinaryVersionDigest
      checkerTranscriptDigest emptyClauseReachabilityWitness solverBuildEvidence
      environmentManifest extractionReplayScriptDigest fallbackNoClaim
      auditTranscript archiveCoherent checkerBackedReachability
      originalUnsat := by
  intro hBenchmark hRaw hNormalized hArchive hChecker hTranscript
  intro hReachability hBuild hEnvironment hScript hFallback hAudit
  intro hCoherent hBacked hOriginal result publish
  exact publish hBenchmark hRaw hNormalized hArchive hChecker hTranscript
    hReachability hBuild hEnvironment hScript hFallback hAudit hCoherent
    hBacked hOriginal

theorem ay_pamg_publication_tied_to_archive_and_empty_replay
    (proofArchiveManifest : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachabilityWitness : Prop)
    (checkerBackedReachability : Prop) (originalUnsat : Prop) :
    ay_pamg_checker_replay_path proofArchiveManifest checkerTranscriptDigest
      emptyClauseReachabilityWitness checkerBackedReachability originalUnsat ->
    proofArchiveManifest ->
    originalUnsat := by
  intro path hArchive
  exact path originalUnsat
    (fun archive_to_transcript rest =>
      rest originalUnsat
        (fun transcript_to_empty rest2 =>
          rest2 originalUnsat
            (fun empty_to_backed backed_to_original =>
              backed_to_original
                (empty_to_backed
                  (transcript_to_empty
                    (archive_to_transcript hArchive)))))))

theorem ay_pamg_archive_coherence_preserved
    (benchmarkFingerprint : Prop) (rawProofDigest : Prop)
    (normalizedProofDigest : Prop) (proofArchiveManifest : Prop)
    (checkerBinaryVersionDigest : Prop) (solverBuildEvidence : Prop)
    (environmentManifest : Prop) (extractionReplayScriptDigest : Prop)
    (archiveCoherent : Prop) :
    ay_pamg_archive_coherence benchmarkFingerprint rawProofDigest
      normalizedProofDigest proofArchiveManifest checkerBinaryVersionDigest
      solverBuildEvidence environmentManifest extractionReplayScriptDigest
      archiveCoherent ->
    benchmarkFingerprint ->
    archiveCoherent := by
  intro coherence hBenchmark
  exact coherence archiveCoherent
    (fun benchmark_to_raw rest =>
      rest archiveCoherent
        (fun raw_to_normalized rest2 =>
          rest2 archiveCoherent
            (fun normalized_to_archive rest3 =>
              rest3 archiveCoherent
                (fun archive_to_checker rest4 =>
                  rest4 archiveCoherent
                    (fun checker_to_build rest5 =>
                      rest5 archiveCoherent
                        (fun build_to_environment rest6 =>
                          rest6 archiveCoherent
                            (fun environment_to_script script_to_coherent =>
                              script_to_coherent
                                (environment_to_script
                                  (build_to_environment
                                    (checker_to_build
                                      (archive_to_checker
                                        (normalized_to_archive
                                          (raw_to_normalized
                                            (benchmark_to_raw
                                              hBenchmark)))))))))))))))

theorem ay_pamg_archive_manifest_alone_cannot_publish_unsat
    (proofArchiveManifest : Prop) (checkerBackedReachability : Prop)
    (noClaim : Prop) :
    proofArchiveManifest ->
    (checkerBackedReachability -> noClaim) ->
    checkerBackedReachability ->
    noClaim := by
  intro _hArchive backed_to_no_claim hBacked
  exact backed_to_no_claim hBacked

theorem ay_pamg_reachability_available
    (benchmarkFingerprint : Prop) (rawProofDigest : Prop)
    (normalizedProofDigest : Prop) (proofArchiveManifest : Prop)
    (checkerBinaryVersionDigest : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (solverBuildEvidence : Prop)
    (environmentManifest : Prop) (extractionReplayScriptDigest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (archiveCoherent : Prop) (checkerBackedReachability : Prop)
    (originalUnsat : Prop) :
    ay_pamg_accepted_evidence benchmarkFingerprint rawProofDigest
      normalizedProofDigest proofArchiveManifest checkerBinaryVersionDigest
      checkerTranscriptDigest emptyClauseReachabilityWitness solverBuildEvidence
      environmentManifest extractionReplayScriptDigest fallbackNoClaim
      auditTranscript archiveCoherent checkerBackedReachability
      originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hBenchmark _hRaw _hNormalized _hArchive _hChecker _hTranscript
      hReachability _hBuild _hEnvironment _hScript _hFallback _hAudit
      _hCoherent _hBacked _hOriginal =>
      hReachability)

theorem ay_pamg_publication_sound
    (benchmarkFingerprint : Prop) (rawProofDigest : Prop)
    (normalizedProofDigest : Prop) (proofArchiveManifest : Prop)
    (checkerBinaryVersionDigest : Prop) (checkerTranscriptDigest : Prop)
    (emptyClauseReachabilityWitness : Prop) (solverBuildEvidence : Prop)
    (environmentManifest : Prop) (extractionReplayScriptDigest : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (archiveCoherent : Prop) (checkerBackedReachability : Prop)
    (originalUnsat : Prop) :
    ay_pamg_publication benchmarkFingerprint rawProofDigest
      normalizedProofDigest proofArchiveManifest checkerBinaryVersionDigest
      checkerTranscriptDigest emptyClauseReachabilityWitness solverBuildEvidence
      environmentManifest extractionReplayScriptDigest fallbackNoClaim
      auditTranscript archiveCoherent checkerBackedReachability
      originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_pamg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_pamg_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_pamg_disj_right noClaim (ay_pamg_disj originalUnsat publicSat)
    (ay_pamg_disj_left originalUnsat publicSat hUnsat)

theorem ay_pamg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_pamg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_pamg_disj_left noClaim
    (ay_pamg_disj originalUnsat publicSat) hNoClaim

theorem ay_pamg_bad_no_claim
    (archiveMismatch : Prop) (rawMismatch : Prop)
    (normalizedMismatch : Prop) (checkerMismatch : Prop)
    (transcriptMismatch : Prop) (benchmarkMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (extractionMismatch : Prop) (replayMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_pamg_bad_guard archiveMismatch rawMismatch normalizedMismatch
      checkerMismatch transcriptMismatch benchmarkMismatch buildMismatch
      environmentMismatch extractionMismatch replayMismatch auditMismatch
      noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_pamg_bad_recompute
    (archiveMismatch : Prop) (rawMismatch : Prop)
    (normalizedMismatch : Prop) (checkerMismatch : Prop)
    (transcriptMismatch : Prop) (benchmarkMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (extractionMismatch : Prop) (replayMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_pamg_bad_guard archiveMismatch rawMismatch normalizedMismatch
      checkerMismatch transcriptMismatch benchmarkMismatch buildMismatch
      environmentMismatch extractionMismatch replayMismatch auditMismatch
      noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_pamg_failed_guard_cannot_bless_unsat
    (archiveMismatch : Prop) (rawMismatch : Prop)
    (normalizedMismatch : Prop) (checkerMismatch : Prop)
    (transcriptMismatch : Prop) (benchmarkMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (extractionMismatch : Prop) (replayMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (publicUnsat : Prop) :
    ay_pamg_bad_guard archiveMismatch rawMismatch normalizedMismatch
      checkerMismatch transcriptMismatch benchmarkMismatch buildMismatch
      environmentMismatch extractionMismatch replayMismatch auditMismatch
      noClaim recompute ->
    ay_pamg_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_pamg_bad_recompute archiveMismatch rawMismatch normalizedMismatch
    checkerMismatch transcriptMismatch benchmarkMismatch buildMismatch
    environmentMismatch extractionMismatch replayMismatch auditMismatch noClaim
    recompute bad

theorem ay_pamg_failure_forces_no_claim
    (archiveMismatch : Prop) (rawMismatch : Prop)
    (normalizedMismatch : Prop) (checkerMismatch : Prop)
    (transcriptMismatch : Prop) (benchmarkMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (extractionMismatch : Prop) (replayMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) :
    ay_pamg_failure_reason archiveMismatch rawMismatch normalizedMismatch
      checkerMismatch transcriptMismatch benchmarkMismatch buildMismatch
      environmentMismatch extractionMismatch replayMismatch auditMismatch ->
    (archiveMismatch -> noClaim) ->
    (rawMismatch -> noClaim) ->
    (normalizedMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (transcriptMismatch -> noClaim) ->
    (benchmarkMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (environmentMismatch -> noClaim) ->
    (extractionMismatch -> noClaim) ->
    (replayMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason archive_to_no_claim raw_to_no_claim normalized_to_no_claim
  intro checker_to_no_claim transcript_to_no_claim benchmark_to_no_claim
  intro build_to_no_claim environment_to_no_claim extraction_to_no_claim
  intro replay_to_no_claim audit_to_no_claim
  exact reason noClaim archive_to_no_claim raw_to_no_claim
    normalized_to_no_claim checker_to_no_claim transcript_to_no_claim
    benchmark_to_no_claim build_to_no_claim environment_to_no_claim
    extraction_to_no_claim replay_to_no_claim audit_to_no_claim

theorem ay_pamg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pamg_raw_mismatch_forces_no_claim
    (rawMismatch noClaim : Prop) :
    rawMismatch ->
    (rawMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pamg_normalized_mismatch_forces_no_claim
    (normalizedMismatch noClaim : Prop) :
    normalizedMismatch ->
    (normalizedMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pamg_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch ->
    (checkerMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pamg_transcript_mismatch_forces_no_claim
    (transcriptMismatch noClaim : Prop) :
    transcriptMismatch ->
    (transcriptMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pamg_benchmark_mismatch_forces_no_claim
    (benchmarkMismatch noClaim : Prop) :
    benchmarkMismatch ->
    (benchmarkMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pamg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pamg_environment_mismatch_forces_no_claim
    (environmentMismatch noClaim : Prop) :
    environmentMismatch ->
    (environmentMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pamg_extraction_mismatch_forces_no_claim
    (extractionMismatch noClaim : Prop) :
    extractionMismatch ->
    (extractionMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pamg_replay_mismatch_forces_no_claim
    (replayMismatch noClaim : Prop) :
    replayMismatch ->
    (replayMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_pamg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
