-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Incremental proof-checker checkpoint guard soundness for ay sequential-main
-- SAT-COMP UNSAT publication. Propositions model proof artifact digests,
-- checkpoint manifests, parser state, live-clause sets, antecedent/reason
-- contexts, replay positions, resumed checker transcripts, final empty-clause
-- reachability, archive/build/environment evidence, fallback recompute and
-- no-claim paths, audit transcripts, and fail-closed diagnostics.

def ay_ipcg_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_ipcg_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_ipcg_map (source : Prop) (target : Prop) :=
  source -> target

def ay_ipcg_accepted_evidence
    (proofArtifactDigest : Prop) (checkpointManifestDigest : Prop)
    (parserStateDigest : Prop) (liveClauseSetDigest : Prop)
    (antecedentReasonContextDigest : Prop) (replayPositionDigest : Prop)
    (resumedCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackRecompute : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (resumedReplayCoherent : Prop) (checkpointContextPreserved : Prop)
    (originalUnsat : Prop) :=
  forall result : Prop,
    (proofArtifactDigest ->
      checkpointManifestDigest ->
      parserStateDigest ->
      liveClauseSetDigest ->
      antecedentReasonContextDigest ->
      replayPositionDigest ->
      resumedCheckerTranscriptDigest ->
      finalEmptyClauseReachabilityWitness ->
      archiveManifest ->
      archiveAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      environmentManifest ->
      environmentAccepted ->
      fallbackRecompute ->
      fallbackNoClaim ->
      auditTranscript ->
      resumedReplayCoherent ->
      checkpointContextPreserved ->
      originalUnsat ->
      result) ->
    result

def ay_ipcg_resumed_replay_path
    (checkpointManifestDigest : Prop) (replayPositionDigest : Prop)
    (resumedCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop)
    (resumedReplayCoherent : Prop) (originalUnsat : Prop) :=
  ay_ipcg_conj
    (ay_ipcg_map checkpointManifestDigest replayPositionDigest)
    (ay_ipcg_conj
      (ay_ipcg_map replayPositionDigest resumedCheckerTranscriptDigest)
      (ay_ipcg_conj
        (ay_ipcg_map resumedCheckerTranscriptDigest resumedReplayCoherent)
        (ay_ipcg_conj
          (ay_ipcg_map resumedReplayCoherent
            finalEmptyClauseReachabilityWitness)
          (ay_ipcg_map finalEmptyClauseReachabilityWitness originalUnsat))))

def ay_ipcg_checkpoint_context
    (checkpointManifestDigest : Prop) (parserStateDigest : Prop)
    (liveClauseSetDigest : Prop) (antecedentReasonContextDigest : Prop)
    (checkpointContextPreserved : Prop) :=
  ay_ipcg_conj
    (ay_ipcg_map checkpointManifestDigest parserStateDigest)
    (ay_ipcg_conj
      (ay_ipcg_map parserStateDigest liveClauseSetDigest)
      (ay_ipcg_conj
        (ay_ipcg_map liveClauseSetDigest antecedentReasonContextDigest)
        (ay_ipcg_map antecedentReasonContextDigest
          checkpointContextPreserved)))

def ay_ipcg_publication
    (proofArtifactDigest : Prop) (checkpointManifestDigest : Prop)
    (parserStateDigest : Prop) (liveClauseSetDigest : Prop)
    (antecedentReasonContextDigest : Prop) (replayPositionDigest : Prop)
    (resumedCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackRecompute : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (resumedReplayCoherent : Prop) (checkpointContextPreserved : Prop)
    (originalUnsat : Prop) :=
  ay_ipcg_conj
    (ay_ipcg_accepted_evidence proofArtifactDigest checkpointManifestDigest
      parserStateDigest liveClauseSetDigest antecedentReasonContextDigest
      replayPositionDigest resumedCheckerTranscriptDigest
      finalEmptyClauseReachabilityWitness archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted environmentManifest environmentAccepted
      fallbackRecompute fallbackNoClaim auditTranscript resumedReplayCoherent
      checkpointContextPreserved originalUnsat)
    originalUnsat

def ay_ipcg_failure_reason
    (proofMismatch : Prop) (checkpointMismatch : Prop)
    (parserMismatch : Prop) (liveMismatch : Prop) (reasonMismatch : Prop)
    (positionMismatch : Prop) (transcriptMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (proofMismatch -> result) ->
    (checkpointMismatch -> result) ->
    (parserMismatch -> result) ->
    (liveMismatch -> result) ->
    (reasonMismatch -> result) ->
    (positionMismatch -> result) ->
    (transcriptMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (archiveMismatch -> result) ->
    (buildMismatch -> result) ->
    (environmentMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_ipcg_bad_guard
    (proofMismatch : Prop) (checkpointMismatch : Prop)
    (parserMismatch : Prop) (liveMismatch : Prop) (reasonMismatch : Prop)
    (positionMismatch : Prop) (transcriptMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :=
  ay_ipcg_conj
    (ay_ipcg_conj noClaim recompute)
    (ay_ipcg_failure_reason proofMismatch checkpointMismatch parserMismatch
      liveMismatch reasonMismatch positionMismatch transcriptMismatch
      reachabilityMismatch archiveMismatch buildMismatch environmentMismatch
      auditMismatch)

def ay_ipcg_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_ipcg_disj noClaim (ay_ipcg_disj originalUnsat publicSat)

theorem ay_ipcg_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_ipcg_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_ipcg_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_ipcg_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_ipcg_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_ipcg_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_ipcg_build_accepted_evidence
    (proofArtifactDigest : Prop) (checkpointManifestDigest : Prop)
    (parserStateDigest : Prop) (liveClauseSetDigest : Prop)
    (antecedentReasonContextDigest : Prop) (replayPositionDigest : Prop)
    (resumedCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackRecompute : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (resumedReplayCoherent : Prop) (checkpointContextPreserved : Prop)
    (originalUnsat : Prop) :
    proofArtifactDigest ->
    checkpointManifestDigest ->
    parserStateDigest ->
    liveClauseSetDigest ->
    antecedentReasonContextDigest ->
    replayPositionDigest ->
    resumedCheckerTranscriptDigest ->
    finalEmptyClauseReachabilityWitness ->
    archiveManifest ->
    archiveAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    environmentManifest ->
    environmentAccepted ->
    fallbackRecompute ->
    fallbackNoClaim ->
    auditTranscript ->
    resumedReplayCoherent ->
    checkpointContextPreserved ->
    originalUnsat ->
    ay_ipcg_accepted_evidence proofArtifactDigest checkpointManifestDigest
      parserStateDigest liveClauseSetDigest antecedentReasonContextDigest
      replayPositionDigest resumedCheckerTranscriptDigest
      finalEmptyClauseReachabilityWitness archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted environmentManifest environmentAccepted
      fallbackRecompute fallbackNoClaim auditTranscript resumedReplayCoherent
      checkpointContextPreserved originalUnsat := by
  intro hProof hCheckpoint hParser hLive hReason hPosition hTranscript
  intro hReachability hArchive hArchiveAccepted hBuild hBuildAccepted
  intro hEnvironment hEnvironmentAccepted hRecompute hNoClaim hAudit
  intro hCoherent hContext hOriginal result publish
  exact publish hProof hCheckpoint hParser hLive hReason hPosition
    hTranscript hReachability hArchive hArchiveAccepted hBuild hBuildAccepted
    hEnvironment hEnvironmentAccepted hRecompute hNoClaim hAudit hCoherent
    hContext hOriginal

theorem ay_ipcg_resumed_checking_publishes_only_with_empty_clause
    (checkpointManifestDigest : Prop) (replayPositionDigest : Prop)
    (resumedCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop)
    (resumedReplayCoherent : Prop) (originalUnsat : Prop) :
    ay_ipcg_resumed_replay_path checkpointManifestDigest replayPositionDigest
      resumedCheckerTranscriptDigest finalEmptyClauseReachabilityWitness
      resumedReplayCoherent originalUnsat ->
    checkpointManifestDigest ->
    originalUnsat := by
  intro path hCheckpoint
  exact path originalUnsat
    (fun checkpoint_to_position rest =>
      rest originalUnsat
        (fun position_to_transcript rest2 =>
          rest2 originalUnsat
            (fun transcript_to_coherent rest3 =>
              rest3 originalUnsat
                (fun coherent_to_reachability reachability_to_original =>
                  reachability_to_original
                    (coherent_to_reachability
                      (transcript_to_coherent
                        (position_to_transcript
                          (checkpoint_to_position hCheckpoint)))))))))

theorem ay_ipcg_checkpoint_state_preserves_checker_context
    (checkpointManifestDigest : Prop) (parserStateDigest : Prop)
    (liveClauseSetDigest : Prop) (antecedentReasonContextDigest : Prop)
    (checkpointContextPreserved : Prop) :
    ay_ipcg_checkpoint_context checkpointManifestDigest parserStateDigest
      liveClauseSetDigest antecedentReasonContextDigest
      checkpointContextPreserved ->
    checkpointManifestDigest ->
    checkpointContextPreserved := by
  intro context hCheckpoint
  exact context checkpointContextPreserved
    (fun checkpoint_to_parser rest =>
      rest checkpointContextPreserved
        (fun parser_to_live rest2 =>
          rest2 checkpointContextPreserved
            (fun live_to_reason reason_to_context =>
              reason_to_context
                (live_to_reason
                  (parser_to_live
                    (checkpoint_to_parser hCheckpoint)))))))

theorem ay_ipcg_final_reachability_available
    (proofArtifactDigest : Prop) (checkpointManifestDigest : Prop)
    (parserStateDigest : Prop) (liveClauseSetDigest : Prop)
    (antecedentReasonContextDigest : Prop) (replayPositionDigest : Prop)
    (resumedCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackRecompute : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (resumedReplayCoherent : Prop) (checkpointContextPreserved : Prop)
    (originalUnsat : Prop) :
    ay_ipcg_accepted_evidence proofArtifactDigest checkpointManifestDigest
      parserStateDigest liveClauseSetDigest antecedentReasonContextDigest
      replayPositionDigest resumedCheckerTranscriptDigest
      finalEmptyClauseReachabilityWitness archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted environmentManifest environmentAccepted
      fallbackRecompute fallbackNoClaim auditTranscript resumedReplayCoherent
      checkpointContextPreserved originalUnsat ->
    finalEmptyClauseReachabilityWitness := by
  intro accepted
  exact accepted finalEmptyClauseReachabilityWitness
    (fun _hProof _hCheckpoint _hParser _hLive _hReason _hPosition
      _hTranscript hReachability _hArchive _hArchiveAccepted _hBuild
      _hBuildAccepted _hEnvironment _hEnvironmentAccepted _hRecompute
      _hNoClaim _hAudit _hCoherent _hContext _hOriginal =>
      hReachability)

theorem ay_ipcg_checkpoint_context_available
    (proofArtifactDigest : Prop) (checkpointManifestDigest : Prop)
    (parserStateDigest : Prop) (liveClauseSetDigest : Prop)
    (antecedentReasonContextDigest : Prop) (replayPositionDigest : Prop)
    (resumedCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackRecompute : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (resumedReplayCoherent : Prop) (checkpointContextPreserved : Prop)
    (originalUnsat : Prop) :
    ay_ipcg_accepted_evidence proofArtifactDigest checkpointManifestDigest
      parserStateDigest liveClauseSetDigest antecedentReasonContextDigest
      replayPositionDigest resumedCheckerTranscriptDigest
      finalEmptyClauseReachabilityWitness archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted environmentManifest environmentAccepted
      fallbackRecompute fallbackNoClaim auditTranscript resumedReplayCoherent
      checkpointContextPreserved originalUnsat ->
    checkpointContextPreserved := by
  intro accepted
  exact accepted checkpointContextPreserved
    (fun _hProof _hCheckpoint _hParser _hLive _hReason _hPosition
      _hTranscript _hReachability _hArchive _hArchiveAccepted _hBuild
      _hBuildAccepted _hEnvironment _hEnvironmentAccepted _hRecompute
      _hNoClaim _hAudit _hCoherent hContext _hOriginal =>
      hContext)

theorem ay_ipcg_publication_sound
    (proofArtifactDigest : Prop) (checkpointManifestDigest : Prop)
    (parserStateDigest : Prop) (liveClauseSetDigest : Prop)
    (antecedentReasonContextDigest : Prop) (replayPositionDigest : Prop)
    (resumedCheckerTranscriptDigest : Prop)
    (finalEmptyClauseReachabilityWitness : Prop) (archiveManifest : Prop)
    (archiveAccepted : Prop) (solverBuildEvidence : Prop)
    (buildAccepted : Prop) (environmentManifest : Prop)
    (environmentAccepted : Prop) (fallbackRecompute : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (resumedReplayCoherent : Prop) (checkpointContextPreserved : Prop)
    (originalUnsat : Prop) :
    ay_ipcg_publication proofArtifactDigest checkpointManifestDigest
      parserStateDigest liveClauseSetDigest antecedentReasonContextDigest
      replayPositionDigest resumedCheckerTranscriptDigest
      finalEmptyClauseReachabilityWitness archiveManifest archiveAccepted
      solverBuildEvidence buildAccepted environmentManifest environmentAccepted
      fallbackRecompute fallbackNoClaim auditTranscript resumedReplayCoherent
      checkpointContextPreserved originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_ipcg_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_ipcg_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_ipcg_disj_right noClaim (ay_ipcg_disj originalUnsat publicSat)
    (ay_ipcg_disj_left originalUnsat publicSat hUnsat)

theorem ay_ipcg_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_ipcg_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_ipcg_disj_left noClaim
    (ay_ipcg_disj originalUnsat publicSat) hNoClaim

theorem ay_ipcg_bad_no_claim
    (proofMismatch : Prop) (checkpointMismatch : Prop)
    (parserMismatch : Prop) (liveMismatch : Prop) (reasonMismatch : Prop)
    (positionMismatch : Prop) (transcriptMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_ipcg_bad_guard proofMismatch checkpointMismatch parserMismatch
      liveMismatch reasonMismatch positionMismatch transcriptMismatch
      reachabilityMismatch archiveMismatch buildMismatch environmentMismatch
      auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_ipcg_bad_recompute
    (proofMismatch : Prop) (checkpointMismatch : Prop)
    (parserMismatch : Prop) (liveMismatch : Prop) (reasonMismatch : Prop)
    (positionMismatch : Prop) (transcriptMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop) :
    ay_ipcg_bad_guard proofMismatch checkpointMismatch parserMismatch
      liveMismatch reasonMismatch positionMismatch transcriptMismatch
      reachabilityMismatch archiveMismatch buildMismatch environmentMismatch
      auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_ipcg_failed_guard_cannot_bless_unsat
    (proofMismatch : Prop) (checkpointMismatch : Prop)
    (parserMismatch : Prop) (liveMismatch : Prop) (reasonMismatch : Prop)
    (positionMismatch : Prop) (transcriptMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) (recompute : Prop)
    (publicUnsat : Prop) :
    ay_ipcg_bad_guard proofMismatch checkpointMismatch parserMismatch
      liveMismatch reasonMismatch positionMismatch transcriptMismatch
      reachabilityMismatch archiveMismatch buildMismatch environmentMismatch
      auditMismatch noClaim recompute ->
    ay_ipcg_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_ipcg_bad_recompute proofMismatch checkpointMismatch parserMismatch
    liveMismatch reasonMismatch positionMismatch transcriptMismatch
    reachabilityMismatch archiveMismatch buildMismatch environmentMismatch
    auditMismatch noClaim recompute bad

theorem ay_ipcg_failure_forces_no_claim
    (proofMismatch : Prop) (checkpointMismatch : Prop)
    (parserMismatch : Prop) (liveMismatch : Prop) (reasonMismatch : Prop)
    (positionMismatch : Prop) (transcriptMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (environmentMismatch : Prop)
    (auditMismatch : Prop) (noClaim : Prop) :
    ay_ipcg_failure_reason proofMismatch checkpointMismatch parserMismatch
      liveMismatch reasonMismatch positionMismatch transcriptMismatch
      reachabilityMismatch archiveMismatch buildMismatch environmentMismatch
      auditMismatch ->
    (proofMismatch -> noClaim) ->
    (checkpointMismatch -> noClaim) ->
    (parserMismatch -> noClaim) ->
    (liveMismatch -> noClaim) ->
    (reasonMismatch -> noClaim) ->
    (positionMismatch -> noClaim) ->
    (transcriptMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (environmentMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason proof_to_no_claim checkpoint_to_no_claim parser_to_no_claim
  intro live_to_no_claim reason_to_no_claim position_to_no_claim
  intro transcript_to_no_claim reachability_to_no_claim archive_to_no_claim
  intro build_to_no_claim environment_to_no_claim audit_to_no_claim
  exact reason noClaim proof_to_no_claim checkpoint_to_no_claim
    parser_to_no_claim live_to_no_claim reason_to_no_claim
    position_to_no_claim transcript_to_no_claim reachability_to_no_claim
    archive_to_no_claim build_to_no_claim environment_to_no_claim
    audit_to_no_claim

theorem ay_ipcg_proof_mismatch_forces_no_claim
    (proofMismatch noClaim : Prop) :
    proofMismatch ->
    (proofMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ipcg_checkpoint_mismatch_forces_no_claim
    (checkpointMismatch noClaim : Prop) :
    checkpointMismatch ->
    (checkpointMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ipcg_parser_mismatch_forces_no_claim
    (parserMismatch noClaim : Prop) :
    parserMismatch ->
    (parserMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ipcg_live_mismatch_forces_no_claim
    (liveMismatch noClaim : Prop) :
    liveMismatch ->
    (liveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ipcg_reason_mismatch_forces_no_claim
    (reasonMismatch noClaim : Prop) :
    reasonMismatch ->
    (reasonMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ipcg_position_mismatch_forces_no_claim
    (positionMismatch noClaim : Prop) :
    positionMismatch ->
    (positionMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ipcg_transcript_mismatch_forces_no_claim
    (transcriptMismatch noClaim : Prop) :
    transcriptMismatch ->
    (transcriptMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ipcg_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch ->
    (reachabilityMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ipcg_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ipcg_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ipcg_environment_mismatch_forces_no_claim
    (environmentMismatch noClaim : Prop) :
    environmentMismatch ->
    (environmentMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ipcg_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
