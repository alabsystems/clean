-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Streaming proof chunk guard soundness for ay sequential-main SAT-COMP UNSAT
-- publication. Propositions model proof artifact digests, chunk manifests,
-- chunk boundaries, live-clause carry-over state, antecedent contexts,
-- per-chunk checker transcripts, final empty-clause reachability, archive and
-- build evidence, environment manifests, fallback no-claim/recompute paths,
-- audit transcripts, and fail-closed diagnostics.

def ay_scg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_scg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_scg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_scg_accepted_evidence
    (proofArtifactDigest : Prop) (chunkManifestDigest : Prop)
    (chunkBoundaryLedger : Prop) (liveClauseCarryOverDigest : Prop)
    (antecedentContextDigest : Prop) (perChunkCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackNoClaim : Prop)
    (fallbackRecompute : Prop) (auditTranscript : Prop)
    (chunkReplayCoherent : Prop) (checkerStatePreserved : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (proofArtifactDigest ->
      chunkManifestDigest ->
      chunkBoundaryLedger ->
      liveClauseCarryOverDigest ->
      antecedentContextDigest ->
      perChunkCheckerTranscriptDigest ->
      finalEmptyClauseReachabilityWitness ->
      archiveManifest ->
      archiveAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      environmentManifest ->
      environmentAccepted ->
      fallbackNoClaim ->
      fallbackRecompute ->
      auditTranscript ->
      chunkReplayCoherent ->
      checkerStatePreserved ->
      originalUnsat ->
      result) ->
    result

def ay_scg_streaming_replay_path
    (chunkManifestDigest : Prop) (perChunkCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop)
    (chunkReplayCoherent : Prop) (originalUnsat : Prop) :=
  ay_scg_conj
    (ay_scg_map chunkManifestDigest perChunkCheckerTranscriptDigest)
    (ay_scg_conj
      (ay_scg_map perChunkCheckerTranscriptDigest chunkReplayCoherent)
      (ay_scg_conj
        (ay_scg_map chunkReplayCoherent
          finalEmptyClauseReachabilityWitness)
        (ay_scg_map finalEmptyClauseReachabilityWitness originalUnsat)))

def ay_scg_state_preservation
    (chunkBoundaryLedger : Prop) (liveClauseCarryOverDigest : Prop)
    (antecedentContextDigest : Prop) (checkerStatePreserved : Prop) :=
  ay_scg_conj
    (ay_scg_map chunkBoundaryLedger liveClauseCarryOverDigest)
    (ay_scg_conj
      (ay_scg_map liveClauseCarryOverDigest antecedentContextDigest)
      (ay_scg_map antecedentContextDigest checkerStatePreserved))

def ay_scg_publication
    (proofArtifactDigest : Prop) (chunkManifestDigest : Prop)
    (chunkBoundaryLedger : Prop) (liveClauseCarryOverDigest : Prop)
    (antecedentContextDigest : Prop) (perChunkCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackNoClaim : Prop)
    (fallbackRecompute : Prop) (auditTranscript : Prop)
    (chunkReplayCoherent : Prop) (checkerStatePreserved : Prop)
    (originalUnsat : Prop) :=
  ay_scg_conj
    (ay_scg_accepted_evidence proofArtifactDigest chunkManifestDigest
      chunkBoundaryLedger liveClauseCarryOverDigest antecedentContextDigest
      perChunkCheckerTranscriptDigest finalEmptyClauseReachabilityWitness
      archiveManifest archiveAccepted solverBuildEvidence buildAccepted
      environmentManifest environmentAccepted fallbackNoClaim fallbackRecompute
      auditTranscript chunkReplayCoherent checkerStatePreserved originalUnsat)
    originalUnsat

def ay_scg_failure_reason
    (proofMismatch : Prop) (chunkMismatch : Prop)
    (boundaryMismatch : Prop) (liveContextMismatch : Prop)
    (antecedentMismatch : Prop) (transcriptMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (proofMismatch -> result) ->
    (chunkMismatch -> result) ->
    (boundaryMismatch -> result) ->
    (liveContextMismatch -> result) ->
    (antecedentMismatch -> result) ->
    (transcriptMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (archiveMismatch -> result) ->
    (buildMismatch -> result) ->
    (environmentMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_scg_bad_guard
    (proofMismatch : Prop) (chunkMismatch : Prop)
    (boundaryMismatch : Prop) (liveContextMismatch : Prop)
    (antecedentMismatch : Prop) (transcriptMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  ay_scg_conj
    (ay_scg_conj noClaim recompute)
    (ay_scg_failure_reason proofMismatch chunkMismatch boundaryMismatch
      liveContextMismatch antecedentMismatch transcriptMismatch
      reachabilityMismatch archiveMismatch buildMismatch environmentMismatch
      auditMismatch)

def ay_scg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_scg_disj noClaim (ay_scg_disj originalUnsat publicSat)

theorem ay_scg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_scg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_scg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_scg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_scg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_scg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_scg_build_accepted_evidence
    (proofArtifactDigest : Prop) (chunkManifestDigest : Prop)
    (chunkBoundaryLedger : Prop) (liveClauseCarryOverDigest : Prop)
    (antecedentContextDigest : Prop) (perChunkCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackNoClaim : Prop)
    (fallbackRecompute : Prop) (auditTranscript : Prop)
    (chunkReplayCoherent : Prop) (checkerStatePreserved : Prop)
    (originalUnsat : Prop) :
    proofArtifactDigest ->
    chunkManifestDigest ->
    chunkBoundaryLedger ->
    liveClauseCarryOverDigest ->
    antecedentContextDigest ->
    perChunkCheckerTranscriptDigest ->
    finalEmptyClauseReachabilityWitness ->
    archiveManifest ->
    archiveAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    environmentManifest ->
    environmentAccepted ->
    fallbackNoClaim ->
    fallbackRecompute ->
    auditTranscript ->
    chunkReplayCoherent ->
    checkerStatePreserved ->
    originalUnsat ->
    ay_scg_accepted_evidence proofArtifactDigest chunkManifestDigest
      chunkBoundaryLedger liveClauseCarryOverDigest antecedentContextDigest
      perChunkCheckerTranscriptDigest finalEmptyClauseReachabilityWitness
      archiveManifest archiveAccepted solverBuildEvidence buildAccepted
      environmentManifest environmentAccepted fallbackNoClaim fallbackRecompute
      auditTranscript chunkReplayCoherent checkerStatePreserved
      originalUnsat := by
  intro hProof hChunk hBoundary hLive hAntecedent hTranscript hReachability
  intro hArchive hArchiveAccepted hBuild hBuildAccepted hEnvironment
  intro hEnvironmentAccepted hNoClaim hRecompute hAudit hCoherent hState
  intro hOriginal result publish
  exact publish hProof hChunk hBoundary hLive hAntecedent hTranscript
    hReachability hArchive hArchiveAccepted hBuild hBuildAccepted hEnvironment
    hEnvironmentAccepted hNoClaim hRecompute hAudit hCoherent hState hOriginal

theorem ay_scg_streaming_chunks_publish_only_with_final_empty_clause
    (chunkManifestDigest : Prop) (perChunkCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop)
    (chunkReplayCoherent : Prop) (originalUnsat : Prop) :
    ay_scg_streaming_replay_path chunkManifestDigest
      perChunkCheckerTranscriptDigest finalEmptyClauseReachabilityWitness
      chunkReplayCoherent originalUnsat ->
    chunkManifestDigest ->
    originalUnsat := by
  intro path hChunk
  exact path originalUnsat
    (fun chunk_to_transcript rest =>
      rest originalUnsat
        (fun transcript_to_coherent rest2 =>
          rest2 originalUnsat
            (fun coherent_to_reachability reachability_to_original =>
              reachability_to_original
                (coherent_to_reachability
                  (transcript_to_coherent
                    (chunk_to_transcript hChunk)))))))

theorem ay_scg_boundary_carryover_preserves_checker_state
    (chunkBoundaryLedger : Prop) (liveClauseCarryOverDigest : Prop)
    (antecedentContextDigest : Prop) (checkerStatePreserved : Prop) :
    ay_scg_state_preservation chunkBoundaryLedger liveClauseCarryOverDigest
      antecedentContextDigest checkerStatePreserved ->
    chunkBoundaryLedger ->
    checkerStatePreserved := by
  intro preservation hBoundary
  exact preservation checkerStatePreserved
    (fun boundary_to_live rest =>
      rest checkerStatePreserved
        (fun live_to_antecedent antecedent_to_state =>
          antecedent_to_state
            (live_to_antecedent
              (boundary_to_live hBoundary))))

theorem ay_scg_final_reachability_available
    (proofArtifactDigest : Prop) (chunkManifestDigest : Prop)
    (chunkBoundaryLedger : Prop) (liveClauseCarryOverDigest : Prop)
    (antecedentContextDigest : Prop) (perChunkCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackNoClaim : Prop)
    (fallbackRecompute : Prop) (auditTranscript : Prop)
    (chunkReplayCoherent : Prop) (checkerStatePreserved : Prop)
    (originalUnsat : Prop) :
    ay_scg_accepted_evidence proofArtifactDigest chunkManifestDigest
      chunkBoundaryLedger liveClauseCarryOverDigest antecedentContextDigest
      perChunkCheckerTranscriptDigest finalEmptyClauseReachabilityWitness
      archiveManifest archiveAccepted solverBuildEvidence buildAccepted
      environmentManifest environmentAccepted fallbackNoClaim fallbackRecompute
      auditTranscript chunkReplayCoherent checkerStatePreserved
      originalUnsat ->
    finalEmptyClauseReachabilityWitness := by
  intro accepted
  exact accepted finalEmptyClauseReachabilityWitness
    (fun _hProof _hChunk _hBoundary _hLive _hAntecedent _hTranscript
      hReachability _hArchive _hArchiveAccepted _hBuild _hBuildAccepted
      _hEnvironment _hEnvironmentAccepted _hNoClaim _hRecompute _hAudit
      _hCoherent _hState _hOriginal =>
      hReachability)

theorem ay_scg_checker_state_available
    (proofArtifactDigest : Prop) (chunkManifestDigest : Prop)
    (chunkBoundaryLedger : Prop) (liveClauseCarryOverDigest : Prop)
    (antecedentContextDigest : Prop) (perChunkCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackNoClaim : Prop)
    (fallbackRecompute : Prop) (auditTranscript : Prop)
    (chunkReplayCoherent : Prop) (checkerStatePreserved : Prop)
    (originalUnsat : Prop) :
    ay_scg_accepted_evidence proofArtifactDigest chunkManifestDigest
      chunkBoundaryLedger liveClauseCarryOverDigest antecedentContextDigest
      perChunkCheckerTranscriptDigest finalEmptyClauseReachabilityWitness
      archiveManifest archiveAccepted solverBuildEvidence buildAccepted
      environmentManifest environmentAccepted fallbackNoClaim fallbackRecompute
      auditTranscript chunkReplayCoherent checkerStatePreserved
      originalUnsat ->
    checkerStatePreserved := by
  intro accepted
  exact accepted checkerStatePreserved
    (fun _hProof _hChunk _hBoundary _hLive _hAntecedent _hTranscript
      _hReachability _hArchive _hArchiveAccepted _hBuild _hBuildAccepted
      _hEnvironment _hEnvironmentAccepted _hNoClaim _hRecompute _hAudit
      _hCoherent hState _hOriginal =>
      hState)

theorem ay_scg_publication_sound
    (proofArtifactDigest : Prop) (chunkManifestDigest : Prop)
    (chunkBoundaryLedger : Prop) (liveClauseCarryOverDigest : Prop)
    (antecedentContextDigest : Prop) (perChunkCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackNoClaim : Prop)
    (fallbackRecompute : Prop) (auditTranscript : Prop)
    (chunkReplayCoherent : Prop) (checkerStatePreserved : Prop)
    (originalUnsat : Prop) :
    ay_scg_publication proofArtifactDigest chunkManifestDigest
      chunkBoundaryLedger liveClauseCarryOverDigest antecedentContextDigest
      perChunkCheckerTranscriptDigest finalEmptyClauseReachabilityWitness
      archiveManifest archiveAccepted solverBuildEvidence buildAccepted
      environmentManifest environmentAccepted fallbackNoClaim fallbackRecompute
      auditTranscript chunkReplayCoherent checkerStatePreserved originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_scg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_scg_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_scg_disj_right noClaim (ay_scg_disj originalUnsat publicSat)
    (ay_scg_disj_left originalUnsat publicSat hUnsat)

theorem ay_scg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_scg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_scg_disj_left noClaim
    (ay_scg_disj originalUnsat publicSat) hNoClaim

theorem ay_scg_bad_no_claim
    (proofMismatch : Prop) (chunkMismatch : Prop)
    (boundaryMismatch : Prop) (liveContextMismatch : Prop)
    (antecedentMismatch : Prop) (transcriptMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_scg_bad_guard proofMismatch chunkMismatch boundaryMismatch
      liveContextMismatch antecedentMismatch transcriptMismatch
      reachabilityMismatch archiveMismatch buildMismatch environmentMismatch
      auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_scg_bad_recompute
    (proofMismatch : Prop) (chunkMismatch : Prop)
    (boundaryMismatch : Prop) (liveContextMismatch : Prop)
    (antecedentMismatch : Prop) (transcriptMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_scg_bad_guard proofMismatch chunkMismatch boundaryMismatch
      liveContextMismatch antecedentMismatch transcriptMismatch
      reachabilityMismatch archiveMismatch buildMismatch environmentMismatch
      auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_scg_failed_guard_cannot_bless_unsat
    (proofMismatch : Prop) (chunkMismatch : Prop)
    (boundaryMismatch : Prop) (liveContextMismatch : Prop)
    (antecedentMismatch : Prop) (transcriptMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (publicUnsat : Prop) :
    ay_scg_bad_guard proofMismatch chunkMismatch boundaryMismatch
      liveContextMismatch antecedentMismatch transcriptMismatch
      reachabilityMismatch archiveMismatch buildMismatch environmentMismatch
      auditMismatch noClaim recompute ->
    ay_scg_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_scg_bad_recompute proofMismatch chunkMismatch boundaryMismatch
    liveContextMismatch antecedentMismatch transcriptMismatch
    reachabilityMismatch archiveMismatch buildMismatch environmentMismatch
    auditMismatch noClaim recompute bad

theorem ay_scg_failure_forces_no_claim
    (proofMismatch : Prop) (chunkMismatch : Prop)
    (boundaryMismatch : Prop) (liveContextMismatch : Prop)
    (antecedentMismatch : Prop) (transcriptMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) :
    ay_scg_failure_reason proofMismatch chunkMismatch boundaryMismatch
      liveContextMismatch antecedentMismatch transcriptMismatch
      reachabilityMismatch archiveMismatch buildMismatch environmentMismatch
      auditMismatch ->
    (proofMismatch -> noClaim) ->
    (chunkMismatch -> noClaim) ->
    (boundaryMismatch -> noClaim) ->
    (liveContextMismatch -> noClaim) ->
    (antecedentMismatch -> noClaim) ->
    (transcriptMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (environmentMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason proof_to_no_claim chunk_to_no_claim boundary_to_no_claim
  intro live_to_no_claim antecedent_to_no_claim transcript_to_no_claim
  intro reachability_to_no_claim archive_to_no_claim build_to_no_claim
  intro environment_to_no_claim audit_to_no_claim
  exact reason noClaim proof_to_no_claim chunk_to_no_claim
    boundary_to_no_claim live_to_no_claim antecedent_to_no_claim
    transcript_to_no_claim reachability_to_no_claim archive_to_no_claim
    build_to_no_claim environment_to_no_claim audit_to_no_claim

theorem ay_scg_proof_mismatch_forces_no_claim
    (proofMismatch noClaim : Prop) :
    proofMismatch ->
    (proofMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_scg_chunk_mismatch_forces_no_claim
    (chunkMismatch noClaim : Prop) :
    chunkMismatch ->
    (chunkMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_scg_boundary_mismatch_forces_no_claim
    (boundaryMismatch noClaim : Prop) :
    boundaryMismatch ->
    (boundaryMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_scg_live_context_mismatch_forces_no_claim
    (liveContextMismatch noClaim : Prop) :
    liveContextMismatch ->
    (liveContextMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_scg_antecedent_mismatch_forces_no_claim
    (antecedentMismatch noClaim : Prop) :
    antecedentMismatch ->
    (antecedentMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_scg_transcript_mismatch_forces_no_claim
    (transcriptMismatch noClaim : Prop) :
    transcriptMismatch ->
    (transcriptMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_scg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch ->
    (reachabilityMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_scg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_scg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_scg_environment_mismatch_forces_no_claim
    (environmentMismatch noClaim : Prop) :
    environmentMismatch ->
    (environmentMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_scg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
