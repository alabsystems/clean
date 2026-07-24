-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded checkpoint/resume soundness for ay sequential-main SAT-COMP UNSAT
-- proof checking. Propositions stand for checker checkpoints, resume offsets,
-- checkpoint digests, parent frontier coverage, chunk manifests, formula
-- fingerprints, checker transcripts, reconstruction evidence, and fail-closed
-- no-claim/recompute diagnostics.

def AyUPCRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPCRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPCRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPCRCheckpointResume
    (checkerCheckpoint : Prop) (resumeOffset : Prop)
    (resumeReplay : Prop) :=
  AyUPCRConj checkerCheckpoint
    (AyUPCRConj
      (AyUPCRMap checkerCheckpoint resumeOffset)
      (AyUPCRMap resumeOffset resumeReplay))

def AyUPCRCheckpointDigest
    (resumeReplay : Prop) (checkpointDigest : Prop)
    (digestAccepted : Prop) :=
  AyUPCRConj
    (AyUPCRMap resumeReplay checkpointDigest)
    (AyUPCRMap checkpointDigest digestAccepted)

def AyUPCRFrontierCoverage
    (resumeReplay : Prop) (frontierParents : Prop)
    (rootEmptyClause : Prop) :=
  AyUPCRConj
    (AyUPCRMap resumeReplay frontierParents)
    (AyUPCRMap frontierParents rootEmptyClause)

def AyUPCRChunkManifest
    (resumeReplay : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) :=
  AyUPCRConj
    (AyUPCRMap resumeReplay chunkManifest)
    (AyUPCRMap chunkManifest manifestAccepted)

def AyUPCRFormulaFingerprint
    (resumeReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUPCRConj
    (AyUPCRMap resumeReplay formulaFingerprint)
    (AyUPCRMap formulaFingerprint fingerprintAccepted)

def AyUPCRCheckerTranscript
    (resumeReplay : Prop) (resumeTranscript : Prop)
    (transcriptAccepted : Prop) :=
  AyUPCRConj
    (AyUPCRMap resumeReplay resumeTranscript)
    (AyUPCRMap resumeTranscript transcriptAccepted)

def AyUPCRReconstruction
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPCRConj reconstructionEvidence
    (AyUPCRConj
      (AyUPCRMap rootEmptyClause visibleUnsat)
      (AyUPCRMap visibleUnsat originalUnsat))

def AyUPCRAcceptedEvidence
    (checkerCheckpoint : Prop) (resumeOffset : Prop)
    (resumeReplay : Prop) (checkpointDigest : Prop)
    (digestAccepted : Prop) (frontierParents : Prop)
    (rootEmptyClause : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (resumeTranscript : Prop)
    (transcriptAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPCRConj
    (AyUPCRCheckpointResume checkerCheckpoint resumeOffset resumeReplay)
    (AyUPCRConj
      (AyUPCRCheckpointDigest resumeReplay checkpointDigest digestAccepted)
      (AyUPCRConj
        (AyUPCRFrontierCoverage resumeReplay frontierParents
          rootEmptyClause)
        (AyUPCRConj
          (AyUPCRChunkManifest resumeReplay chunkManifest manifestAccepted)
          (AyUPCRConj
            (AyUPCRFormulaFingerprint resumeReplay formulaFingerprint
              fingerprintAccepted)
            (AyUPCRConj
              (AyUPCRCheckerTranscript resumeReplay resumeTranscript
                transcriptAccepted)
              (AyUPCRReconstruction rootEmptyClause reconstructionEvidence
                visibleUnsat originalUnsat)))))))

def AyUPCRAcceptedResume
    (checkerCheckpoint : Prop) (resumeOffset : Prop)
    (resumeReplay : Prop) (checkpointDigest : Prop)
    (digestAccepted : Prop) (frontierParents : Prop)
    (rootEmptyClause : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (resumeTranscript : Prop)
    (transcriptAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPCRConj
    (AyUPCRAcceptedEvidence checkerCheckpoint resumeOffset resumeReplay
      checkpointDigest digestAccepted frontierParents rootEmptyClause
      chunkManifest manifestAccepted formulaFingerprint fingerprintAccepted
      resumeTranscript transcriptAccepted reconstructionEvidence visibleUnsat
      originalUnsat)
    originalUnsat

def AyUPCRBadResume
    (staleCheckpoint : Prop) (badOffset : Prop)
    (missingFrontierParent : Prop) (digestMismatch : Prop)
    (fingerprintMismatch : Prop) (uncheckedResumeTranscript : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  AyUPCRConj
    (AyUPCRConj noClaim recompute)
    (AyUPCRDisj staleCheckpoint
      (AyUPCRDisj badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript)))))

def AyUPCRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUPCRDisj noClaim originalUnsat

theorem ay_upcr_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPCRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_upcr_conj_left
    (p : Prop) (q : Prop) :
    AyUPCRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_upcr_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPCRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_upcr_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPCRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_upcr_checker_checkpoint
    (checkerCheckpoint : Prop) (resumeOffset : Prop)
    (resumeReplay : Prop) :
    AyUPCRCheckpointResume checkerCheckpoint resumeOffset resumeReplay ->
    checkerCheckpoint := by
  intro resume
  exact resume checkerCheckpoint
    (fun checkpoint _tail => checkpoint)

theorem ay_upcr_resume_offset
    (checkerCheckpoint : Prop) (resumeOffset : Prop)
    (resumeReplay : Prop) :
    AyUPCRCheckpointResume checkerCheckpoint resumeOffset resumeReplay ->
    resumeOffset := by
  intro resume
  exact resume resumeOffset
    (fun (checkpoint : checkerCheckpoint) tail =>
      tail resumeOffset
        (fun checkpoint_to_offset _offset_to_replay =>
          checkpoint_to_offset checkpoint))

theorem ay_upcr_resume_replay
    (checkerCheckpoint : Prop) (resumeOffset : Prop)
    (resumeReplay : Prop) :
    AyUPCRCheckpointResume checkerCheckpoint resumeOffset resumeReplay ->
    resumeReplay := by
  intro resume
  exact resume resumeReplay
    (fun (checkpoint : checkerCheckpoint) tail =>
      tail resumeReplay
        (fun checkpoint_to_offset offset_to_replay =>
          offset_to_replay (checkpoint_to_offset checkpoint)))

theorem ay_upcr_checkpoint_digest
    (resumeReplay : Prop) (checkpointDigest : Prop)
    (digestAccepted : Prop) :
    AyUPCRCheckpointDigest resumeReplay checkpointDigest digestAccepted ->
    resumeReplay ->
    checkpointDigest := by
  intro digest
  exact digest (resumeReplay -> checkpointDigest)
    (fun replay_to_digest _digest_to_accept => replay_to_digest)

theorem ay_upcr_digest_accepted
    (resumeReplay : Prop) (checkpointDigest : Prop)
    (digestAccepted : Prop) :
    AyUPCRCheckpointDigest resumeReplay checkpointDigest digestAccepted ->
    checkpointDigest ->
    digestAccepted := by
  intro digest
  exact digest (checkpointDigest -> digestAccepted)
    (fun _replay_to_digest digest_to_accept => digest_to_accept)

theorem ay_upcr_frontier_parents
    (resumeReplay : Prop) (frontierParents : Prop)
    (rootEmptyClause : Prop) :
    AyUPCRFrontierCoverage resumeReplay frontierParents rootEmptyClause ->
    resumeReplay ->
    frontierParents := by
  intro frontier
  exact frontier (resumeReplay -> frontierParents)
    (fun replay_to_frontier _frontier_to_root => replay_to_frontier)

theorem ay_upcr_root_empty_clause
    (resumeReplay : Prop) (frontierParents : Prop)
    (rootEmptyClause : Prop) :
    AyUPCRFrontierCoverage resumeReplay frontierParents rootEmptyClause ->
    frontierParents ->
    rootEmptyClause := by
  intro frontier
  exact frontier (frontierParents -> rootEmptyClause)
    (fun _replay_to_frontier frontier_to_root => frontier_to_root)

theorem ay_upcr_chunk_manifest
    (resumeReplay : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) :
    AyUPCRChunkManifest resumeReplay chunkManifest manifestAccepted ->
    resumeReplay ->
    chunkManifest := by
  intro manifest
  exact manifest (resumeReplay -> chunkManifest)
    (fun replay_to_manifest _manifest_to_accept => replay_to_manifest)

theorem ay_upcr_manifest_accepted
    (resumeReplay : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) :
    AyUPCRChunkManifest resumeReplay chunkManifest manifestAccepted ->
    chunkManifest ->
    manifestAccepted := by
  intro manifest
  exact manifest (chunkManifest -> manifestAccepted)
    (fun _replay_to_manifest manifest_to_accept => manifest_to_accept)

theorem ay_upcr_formula_fingerprint
    (resumeReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUPCRFormulaFingerprint resumeReplay formulaFingerprint
      fingerprintAccepted ->
    resumeReplay ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (resumeReplay -> formulaFingerprint)
    (fun replay_to_fingerprint _fingerprint_to_accept =>
      replay_to_fingerprint)

theorem ay_upcr_fingerprint_accepted
    (resumeReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUPCRFormulaFingerprint resumeReplay formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _replay_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_upcr_resume_transcript
    (resumeReplay : Prop) (resumeTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUPCRCheckerTranscript resumeReplay resumeTranscript
      transcriptAccepted ->
    resumeReplay ->
    resumeTranscript := by
  intro transcript
  exact transcript (resumeReplay -> resumeTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_upcr_transcript_accepted
    (resumeReplay : Prop) (resumeTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUPCRCheckerTranscript resumeReplay resumeTranscript
      transcriptAccepted ->
    resumeTranscript ->
    transcriptAccepted := by
  intro transcript
  exact transcript (resumeTranscript -> transcriptAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_upcr_reconstruction_evidence
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPCRReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_upcr_conj_left reconstructionEvidence
    (AyUPCRConj
      (AyUPCRMap rootEmptyClause visibleUnsat)
      (AyUPCRMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_upcr_visible_unsat_from_root
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPCRReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    rootEmptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (rootEmptyClause -> visibleUnsat)
    (fun _evidence tail =>
      tail (rootEmptyClause -> visibleUnsat)
        (fun root_to_visible _visible_to_original => root_to_visible))

theorem ay_upcr_original_unsat_from_visible
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPCRReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _evidence tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _root_to_visible visible_to_original => visible_to_original))

theorem ay_upcr_accepted_evidence
    (checkerCheckpoint : Prop) (resumeOffset : Prop)
    (resumeReplay : Prop) (checkpointDigest : Prop)
    (digestAccepted : Prop) (frontierParents : Prop)
    (rootEmptyClause : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (resumeTranscript : Prop)
    (transcriptAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPCRAcceptedResume checkerCheckpoint resumeOffset resumeReplay
      checkpointDigest digestAccepted frontierParents rootEmptyClause
      chunkManifest manifestAccepted formulaFingerprint fingerprintAccepted
      resumeTranscript transcriptAccepted reconstructionEvidence visibleUnsat
      originalUnsat ->
    AyUPCRAcceptedEvidence checkerCheckpoint resumeOffset resumeReplay
      checkpointDigest digestAccepted frontierParents rootEmptyClause
      chunkManifest manifestAccepted formulaFingerprint fingerprintAccepted
      resumeTranscript transcriptAccepted reconstructionEvidence visibleUnsat
      originalUnsat := by
  intro accepted
  exact ay_upcr_conj_left
    (AyUPCRAcceptedEvidence checkerCheckpoint resumeOffset resumeReplay
      checkpointDigest digestAccepted frontierParents rootEmptyClause
      chunkManifest manifestAccepted formulaFingerprint fingerprintAccepted
      resumeTranscript transcriptAccepted reconstructionEvidence visibleUnsat
      originalUnsat)
    originalUnsat
    accepted

theorem ay_upcr_accepted_original_unsat
    (checkerCheckpoint : Prop) (resumeOffset : Prop)
    (resumeReplay : Prop) (checkpointDigest : Prop)
    (digestAccepted : Prop) (frontierParents : Prop)
    (rootEmptyClause : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (resumeTranscript : Prop)
    (transcriptAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPCRAcceptedResume checkerCheckpoint resumeOffset resumeReplay
      checkpointDigest digestAccepted frontierParents rootEmptyClause
      chunkManifest manifestAccepted formulaFingerprint fingerprintAccepted
      resumeTranscript transcriptAccepted reconstructionEvidence visibleUnsat
      originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_upcr_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUPCRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_upcr_disj_right noClaim originalUnsat unsat

theorem ay_upcr_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUPCRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_upcr_disj_left noClaim originalUnsat no_claim

theorem ay_upcr_accepted_resume_publish_sound
    (checkerCheckpoint : Prop) (resumeOffset : Prop)
    (resumeReplay : Prop) (checkpointDigest : Prop)
    (digestAccepted : Prop) (frontierParents : Prop)
    (rootEmptyClause : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (resumeTranscript : Prop)
    (transcriptAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUPCRAcceptedResume checkerCheckpoint resumeOffset resumeReplay
      checkpointDigest digestAccepted frontierParents rootEmptyClause
      chunkManifest manifestAccepted formulaFingerprint fingerprintAccepted
      resumeTranscript transcriptAccepted reconstructionEvidence visibleUnsat
      originalUnsat ->
    AyUPCRPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_upcr_public_unsat_report noClaim originalUnsat
    (ay_upcr_accepted_original_unsat checkerCheckpoint resumeOffset
      resumeReplay checkpointDigest digestAccepted frontierParents
      rootEmptyClause chunkManifest manifestAccepted formulaFingerprint
      fingerprintAccepted resumeTranscript transcriptAccepted
      reconstructionEvidence visibleUnsat originalUnsat accepted)

theorem ay_upcr_bad_resume_no_claim
    (staleCheckpoint : Prop) (badOffset : Prop)
    (missingFrontierParent : Prop) (digestMismatch : Prop)
    (fingerprintMismatch : Prop) (uncheckedResumeTranscript : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPCRBadResume staleCheckpoint badOffset missingFrontierParent
      digestMismatch fingerprintMismatch uncheckedResumeTranscript noClaim
      recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_upcr_conj_left noClaim recompute fail_closed)

theorem ay_upcr_bad_resume_recompute
    (staleCheckpoint : Prop) (badOffset : Prop)
    (missingFrontierParent : Prop) (digestMismatch : Prop)
    (fingerprintMismatch : Prop) (uncheckedResumeTranscript : Prop)
    (noClaim : Prop) (recompute : Prop) :
    AyUPCRBadResume staleCheckpoint badOffset missingFrontierParent
      digestMismatch fingerprintMismatch uncheckedResumeTranscript noClaim
      recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_upcr_bad_resume_public_no_claim
    (staleCheckpoint : Prop) (badOffset : Prop)
    (missingFrontierParent : Prop) (digestMismatch : Prop)
    (fingerprintMismatch : Prop) (uncheckedResumeTranscript : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPCRBadResume staleCheckpoint badOffset missingFrontierParent
      digestMismatch fingerprintMismatch uncheckedResumeTranscript noClaim
      recompute ->
    AyUPCRPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_upcr_public_no_claim_report noClaim originalUnsat
    (ay_upcr_bad_resume_no_claim staleCheckpoint badOffset
      missingFrontierParent digestMismatch fingerprintMismatch
      uncheckedResumeTranscript noClaim recompute bad)

theorem ay_upcr_bad_resume_cannot_publish
    (staleCheckpoint : Prop) (badOffset : Prop)
    (missingFrontierParent : Prop) (digestMismatch : Prop)
    (fingerprintMismatch : Prop) (uncheckedResumeTranscript : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPCRBadResume staleCheckpoint badOffset missingFrontierParent
      digestMismatch fingerprintMismatch uncheckedResumeTranscript noClaim
      recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_upcr_bad_resume_no_claim staleCheckpoint badOffset
      missingFrontierParent digestMismatch fingerprintMismatch
      uncheckedResumeTranscript noClaim recompute bad)
    unsat

theorem ay_upcr_stale_checkpoint_forces_no_claim
    (staleCheckpoint : Prop) (badOffset : Prop)
    (missingFrontierParent : Prop) (digestMismatch : Prop)
    (fingerprintMismatch : Prop) (uncheckedResumeTranscript : Prop)
    (noClaim : Prop) (recompute : Prop) :
    staleCheckpoint ->
    AyUPCRConj noClaim recompute ->
    AyUPCRBadResume staleCheckpoint badOffset missingFrontierParent
      digestMismatch fingerprintMismatch uncheckedResumeTranscript noClaim
      recompute := by
  intro stale
  intro fail_closed
  exact ay_upcr_conj_intro
    (AyUPCRConj noClaim recompute)
    (AyUPCRDisj staleCheckpoint
      (AyUPCRDisj badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript)))))
    fail_closed
    (ay_upcr_disj_left staleCheckpoint
      (AyUPCRDisj badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript))))
      stale)

theorem ay_upcr_bad_offset_forces_no_claim
    (staleCheckpoint : Prop) (badOffset : Prop)
    (missingFrontierParent : Prop) (digestMismatch : Prop)
    (fingerprintMismatch : Prop) (uncheckedResumeTranscript : Prop)
    (noClaim : Prop) (recompute : Prop) :
    badOffset ->
    AyUPCRConj noClaim recompute ->
    AyUPCRBadResume staleCheckpoint badOffset missingFrontierParent
      digestMismatch fingerprintMismatch uncheckedResumeTranscript noClaim
      recompute := by
  intro bad_offset
  intro fail_closed
  exact ay_upcr_conj_intro
    (AyUPCRConj noClaim recompute)
    (AyUPCRDisj staleCheckpoint
      (AyUPCRDisj badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript)))))
    fail_closed
    (ay_upcr_disj_right staleCheckpoint
      (AyUPCRDisj badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript))))
      (ay_upcr_disj_left badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript)))
        bad_offset))

theorem ay_upcr_missing_frontier_parent_forces_no_claim
    (staleCheckpoint : Prop) (badOffset : Prop)
    (missingFrontierParent : Prop) (digestMismatch : Prop)
    (fingerprintMismatch : Prop) (uncheckedResumeTranscript : Prop)
    (noClaim : Prop) (recompute : Prop) :
    missingFrontierParent ->
    AyUPCRConj noClaim recompute ->
    AyUPCRBadResume staleCheckpoint badOffset missingFrontierParent
      digestMismatch fingerprintMismatch uncheckedResumeTranscript noClaim
      recompute := by
  intro missing_parent
  intro fail_closed
  exact ay_upcr_conj_intro
    (AyUPCRConj noClaim recompute)
    (AyUPCRDisj staleCheckpoint
      (AyUPCRDisj badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript)))))
    fail_closed
    (ay_upcr_disj_right staleCheckpoint
      (AyUPCRDisj badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript))))
      (ay_upcr_disj_right badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript)))
        (ay_upcr_disj_left missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript))
          missing_parent)))

theorem ay_upcr_digest_mismatch_forces_no_claim
    (staleCheckpoint : Prop) (badOffset : Prop)
    (missingFrontierParent : Prop) (digestMismatch : Prop)
    (fingerprintMismatch : Prop) (uncheckedResumeTranscript : Prop)
    (noClaim : Prop) (recompute : Prop) :
    digestMismatch ->
    AyUPCRConj noClaim recompute ->
    AyUPCRBadResume staleCheckpoint badOffset missingFrontierParent
      digestMismatch fingerprintMismatch uncheckedResumeTranscript noClaim
      recompute := by
  intro mismatch
  intro fail_closed
  exact ay_upcr_conj_intro
    (AyUPCRConj noClaim recompute)
    (AyUPCRDisj staleCheckpoint
      (AyUPCRDisj badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript)))))
    fail_closed
    (ay_upcr_disj_right staleCheckpoint
      (AyUPCRDisj badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript))))
      (ay_upcr_disj_right badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript)))
        (ay_upcr_disj_right missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript))
          (ay_upcr_disj_left digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript)
            mismatch))))

theorem ay_upcr_unchecked_resume_transcript_forces_no_claim
    (staleCheckpoint : Prop) (badOffset : Prop)
    (missingFrontierParent : Prop) (digestMismatch : Prop)
    (fingerprintMismatch : Prop) (uncheckedResumeTranscript : Prop)
    (noClaim : Prop) (recompute : Prop) :
    uncheckedResumeTranscript ->
    AyUPCRConj noClaim recompute ->
    AyUPCRBadResume staleCheckpoint badOffset missingFrontierParent
      digestMismatch fingerprintMismatch uncheckedResumeTranscript noClaim
      recompute := by
  intro unchecked
  intro fail_closed
  exact ay_upcr_conj_intro
    (AyUPCRConj noClaim recompute)
    (AyUPCRDisj staleCheckpoint
      (AyUPCRDisj badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript)))))
    fail_closed
    (ay_upcr_disj_right staleCheckpoint
      (AyUPCRDisj badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript))))
      (ay_upcr_disj_right badOffset
        (AyUPCRDisj missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript)))
        (ay_upcr_disj_right missingFrontierParent
          (AyUPCRDisj digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript))
          (ay_upcr_disj_right digestMismatch
            (AyUPCRDisj fingerprintMismatch uncheckedResumeTranscript)
            (ay_upcr_disj_right fingerprintMismatch uncheckedResumeTranscript
              unchecked)))))

theorem ay_upcr_unchecked_resume_transcript_cannot_publish
    (staleCheckpoint : Prop) (badOffset : Prop)
    (missingFrontierParent : Prop) (digestMismatch : Prop)
    (fingerprintMismatch : Prop) (uncheckedResumeTranscript : Prop)
    (noClaim : Prop) (recompute : Prop) (originalUnsat : Prop) :
    AyUPCRBadResume staleCheckpoint badOffset missingFrontierParent
      digestMismatch fingerprintMismatch uncheckedResumeTranscript noClaim
      recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_upcr_bad_resume_cannot_publish staleCheckpoint badOffset
    missingFrontierParent digestMismatch fingerprintMismatch
    uncheckedResumeTranscript noClaim recompute originalUnsat bad
