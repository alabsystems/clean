-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded UNSAT checker streaming-window soundness for ay sequential-main
-- SAT-COMP checking. Propositions stand for window manifests, parent
-- availability, digest coverage, checkpoint transcripts, formula fingerprints,
-- reconstruction evidence, and fail-closed no-claim/recompute diagnostics.

def AyUCSWConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCSWDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCSWMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCSWWindowManifest
    (windowManifest : Prop) (windowChunks : Prop)
    (windowReplay : Prop) :=
  AyUCSWConj windowManifest
    (AyUCSWConj
      (AyUCSWMap windowManifest windowChunks)
      (AyUCSWMap windowChunks windowReplay))

def AyUCSWParentAvailability
    (windowReplay : Prop) (parentAvailable : Prop)
    (rootEmptyClause : Prop) :=
  AyUCSWConj
    (AyUCSWMap windowReplay parentAvailable)
    (AyUCSWMap parentAvailable rootEmptyClause)

def AyUCSWDigestCoverage
    (windowReplay : Prop) (digestCoverage : Prop)
    (digestAccepted : Prop) :=
  AyUCSWConj
    (AyUCSWMap windowReplay digestCoverage)
    (AyUCSWMap digestCoverage digestAccepted)

def AyUCSWCheckpointTranscript
    (windowReplay : Prop) (checkpointTranscript : Prop)
    (transcriptAccepted : Prop) :=
  AyUCSWConj
    (AyUCSWMap windowReplay checkpointTranscript)
    (AyUCSWMap checkpointTranscript transcriptAccepted)

def AyUCSWFormulaFingerprint
    (windowReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUCSWConj
    (AyUCSWMap windowReplay formulaFingerprint)
    (AyUCSWMap formulaFingerprint fingerprintAccepted)

def AyUCSWReconstruction
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCSWConj reconstructionEvidence
    (AyUCSWConj
      (AyUCSWMap rootEmptyClause visibleUnsat)
      (AyUCSWMap visibleUnsat originalUnsat))

def AyUCSWAcceptedEvidence
    (windowManifest : Prop) (windowChunks : Prop)
    (windowReplay : Prop) (parentAvailable : Prop)
    (rootEmptyClause : Prop) (digestCoverage : Prop)
    (digestAccepted : Prop) (checkpointTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCSWConj
    (AyUCSWWindowManifest windowManifest windowChunks windowReplay)
    (AyUCSWConj
      (AyUCSWParentAvailability windowReplay parentAvailable
        rootEmptyClause)
      (AyUCSWConj
        (AyUCSWDigestCoverage windowReplay digestCoverage digestAccepted)
        (AyUCSWConj
          (AyUCSWCheckpointTranscript windowReplay checkpointTranscript
            transcriptAccepted)
          (AyUCSWConj
            (AyUCSWFormulaFingerprint windowReplay formulaFingerprint
              fingerprintAccepted)
            (AyUCSWReconstruction rootEmptyClause reconstructionEvidence
              visibleUnsat originalUnsat)))))

def AyUCSWAcceptedWindow
    (windowManifest : Prop) (windowChunks : Prop)
    (windowReplay : Prop) (parentAvailable : Prop)
    (rootEmptyClause : Prop) (digestCoverage : Prop)
    (digestAccepted : Prop) (checkpointTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCSWConj
    (AyUCSWAcceptedEvidence windowManifest windowChunks windowReplay
      parentAvailable rootEmptyClause digestCoverage digestAccepted
      checkpointTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat)
    originalUnsat

def AyUCSWBadWindow
    (missingParentAcrossWindow : Prop) (droppedDigest : Prop)
    (staleCheckpoint : Prop) (fingerprintMismatch : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUCSWConj
    (AyUCSWConj noClaim recompute)
    (AyUCSWDisj missingParentAcrossWindow
      (AyUCSWDisj droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript))))

def AyUCSWPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCSWDisj noClaim originalUnsat

theorem ay_ucsw_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCSWConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucsw_conj_left
    (p : Prop) (q : Prop) :
    AyUCSWConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucsw_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCSWDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucsw_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCSWDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucsw_window_manifest
    (windowManifest : Prop) (windowChunks : Prop)
    (windowReplay : Prop) :
    AyUCSWWindowManifest windowManifest windowChunks windowReplay ->
    windowManifest := by
  intro manifest
  exact manifest windowManifest
    (fun manifest_proof _tail => manifest_proof)

theorem ay_ucsw_window_chunks
    (windowManifest : Prop) (windowChunks : Prop)
    (windowReplay : Prop) :
    AyUCSWWindowManifest windowManifest windowChunks windowReplay ->
    windowChunks := by
  intro manifest
  exact manifest windowChunks
    (fun (manifest_proof : windowManifest) tail =>
      tail windowChunks
        (fun manifest_to_chunks _chunks_to_replay =>
          manifest_to_chunks manifest_proof))

theorem ay_ucsw_window_replay
    (windowManifest : Prop) (windowChunks : Prop)
    (windowReplay : Prop) :
    AyUCSWWindowManifest windowManifest windowChunks windowReplay ->
    windowReplay := by
  intro manifest
  exact manifest windowReplay
    (fun (manifest_proof : windowManifest) tail =>
      tail windowReplay
        (fun manifest_to_chunks chunks_to_replay =>
          chunks_to_replay (manifest_to_chunks manifest_proof)))

theorem ay_ucsw_parent_available
    (windowReplay : Prop) (parentAvailable : Prop)
    (rootEmptyClause : Prop) :
    AyUCSWParentAvailability windowReplay parentAvailable rootEmptyClause ->
    windowReplay ->
    parentAvailable := by
  intro parents
  exact parents (windowReplay -> parentAvailable)
    (fun replay_to_parent _parent_to_root => replay_to_parent)

theorem ay_ucsw_root_empty_clause
    (windowReplay : Prop) (parentAvailable : Prop)
    (rootEmptyClause : Prop) :
    AyUCSWParentAvailability windowReplay parentAvailable rootEmptyClause ->
    parentAvailable ->
    rootEmptyClause := by
  intro parents
  exact parents (parentAvailable -> rootEmptyClause)
    (fun _replay_to_parent parent_to_root => parent_to_root)

theorem ay_ucsw_digest_coverage
    (windowReplay : Prop) (digestCoverage : Prop)
    (digestAccepted : Prop) :
    AyUCSWDigestCoverage windowReplay digestCoverage digestAccepted ->
    windowReplay ->
    digestCoverage := by
  intro digest
  exact digest (windowReplay -> digestCoverage)
    (fun replay_to_digest _digest_to_accept => replay_to_digest)

theorem ay_ucsw_digest_accepted
    (windowReplay : Prop) (digestCoverage : Prop)
    (digestAccepted : Prop) :
    AyUCSWDigestCoverage windowReplay digestCoverage digestAccepted ->
    digestCoverage ->
    digestAccepted := by
  intro digest
  exact digest (digestCoverage -> digestAccepted)
    (fun _replay_to_digest digest_to_accept => digest_to_accept)

theorem ay_ucsw_checkpoint_transcript
    (windowReplay : Prop) (checkpointTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUCSWCheckpointTranscript windowReplay checkpointTranscript
      transcriptAccepted ->
    windowReplay ->
    checkpointTranscript := by
  intro transcript
  exact transcript (windowReplay -> checkpointTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_ucsw_transcript_accepted
    (windowReplay : Prop) (checkpointTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUCSWCheckpointTranscript windowReplay checkpointTranscript
      transcriptAccepted ->
    checkpointTranscript ->
    transcriptAccepted := by
  intro transcript
  exact transcript (checkpointTranscript -> transcriptAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_ucsw_formula_fingerprint
    (windowReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUCSWFormulaFingerprint windowReplay formulaFingerprint
      fingerprintAccepted ->
    windowReplay ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (windowReplay -> formulaFingerprint)
    (fun replay_to_fingerprint _fingerprint_to_accept =>
      replay_to_fingerprint)

theorem ay_ucsw_fingerprint_accepted
    (windowReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUCSWFormulaFingerprint windowReplay formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _replay_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_ucsw_reconstruction_evidence
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCSWReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_ucsw_conj_left reconstructionEvidence
    (AyUCSWConj
      (AyUCSWMap rootEmptyClause visibleUnsat)
      (AyUCSWMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_ucsw_visible_unsat_from_root
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCSWReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    rootEmptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (rootEmptyClause -> visibleUnsat)
    (fun _evidence tail =>
      tail (rootEmptyClause -> visibleUnsat)
        (fun root_to_visible _visible_to_original => root_to_visible))

theorem ay_ucsw_original_unsat_from_visible
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCSWReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _evidence tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _root_to_visible visible_to_original => visible_to_original))

theorem ay_ucsw_accepted_evidence
    (windowManifest : Prop) (windowChunks : Prop)
    (windowReplay : Prop) (parentAvailable : Prop)
    (rootEmptyClause : Prop) (digestCoverage : Prop)
    (digestAccepted : Prop) (checkpointTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCSWAcceptedWindow windowManifest windowChunks windowReplay
      parentAvailable rootEmptyClause digestCoverage digestAccepted
      checkpointTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat ->
    AyUCSWAcceptedEvidence windowManifest windowChunks windowReplay
      parentAvailable rootEmptyClause digestCoverage digestAccepted
      checkpointTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat := by
  intro accepted
  exact ay_ucsw_conj_left
    (AyUCSWAcceptedEvidence windowManifest windowChunks windowReplay
      parentAvailable rootEmptyClause digestCoverage digestAccepted
      checkpointTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_ucsw_accepted_original_unsat
    (windowManifest : Prop) (windowChunks : Prop)
    (windowReplay : Prop) (parentAvailable : Prop)
    (rootEmptyClause : Prop) (digestCoverage : Prop)
    (digestAccepted : Prop) (checkpointTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCSWAcceptedWindow windowManifest windowChunks windowReplay
      parentAvailable rootEmptyClause digestCoverage digestAccepted
      checkpointTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_ucsw_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUCSWPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucsw_disj_right noClaim originalUnsat unsat

theorem ay_ucsw_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUCSWPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucsw_disj_left noClaim originalUnsat no_claim

theorem ay_ucsw_accepted_window_publish_sound
    (windowManifest : Prop) (windowChunks : Prop)
    (windowReplay : Prop) (parentAvailable : Prop)
    (rootEmptyClause : Prop) (digestCoverage : Prop)
    (digestAccepted : Prop) (checkpointTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUCSWAcceptedWindow windowManifest windowChunks windowReplay
      parentAvailable rootEmptyClause digestCoverage digestAccepted
      checkpointTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat ->
    AyUCSWPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_ucsw_public_unsat_report noClaim originalUnsat
    (ay_ucsw_accepted_original_unsat windowManifest windowChunks
      windowReplay parentAvailable rootEmptyClause digestCoverage
      digestAccepted checkpointTranscript transcriptAccepted
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat accepted)

theorem ay_ucsw_bad_window_no_claim
    (missingParentAcrossWindow : Prop) (droppedDigest : Prop)
    (staleCheckpoint : Prop) (fingerprintMismatch : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCSWBadWindow missingParentAcrossWindow droppedDigest staleCheckpoint
      fingerprintMismatch uncheckedTranscript noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_ucsw_conj_left noClaim recompute fail_closed)

theorem ay_ucsw_bad_window_recompute
    (missingParentAcrossWindow : Prop) (droppedDigest : Prop)
    (staleCheckpoint : Prop) (fingerprintMismatch : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCSWBadWindow missingParentAcrossWindow droppedDigest staleCheckpoint
      fingerprintMismatch uncheckedTranscript noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_ucsw_bad_window_public_no_claim
    (missingParentAcrossWindow : Prop) (droppedDigest : Prop)
    (staleCheckpoint : Prop) (fingerprintMismatch : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUCSWBadWindow missingParentAcrossWindow droppedDigest staleCheckpoint
      fingerprintMismatch uncheckedTranscript noClaim recompute ->
    AyUCSWPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucsw_public_no_claim_report noClaim originalUnsat
    (ay_ucsw_bad_window_no_claim missingParentAcrossWindow droppedDigest
      staleCheckpoint fingerprintMismatch uncheckedTranscript noClaim
      recompute bad)

theorem ay_ucsw_bad_window_cannot_publish
    (missingParentAcrossWindow : Prop) (droppedDigest : Prop)
    (staleCheckpoint : Prop) (fingerprintMismatch : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUCSWBadWindow missingParentAcrossWindow droppedDigest staleCheckpoint
      fingerprintMismatch uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_ucsw_bad_window_no_claim missingParentAcrossWindow droppedDigest
      staleCheckpoint fingerprintMismatch uncheckedTranscript noClaim
      recompute bad)
    unsat

theorem ay_ucsw_missing_parent_forces_no_claim
    (missingParentAcrossWindow : Prop) (droppedDigest : Prop)
    (staleCheckpoint : Prop) (fingerprintMismatch : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    missingParentAcrossWindow ->
    AyUCSWConj noClaim recompute ->
    AyUCSWBadWindow missingParentAcrossWindow droppedDigest staleCheckpoint
      fingerprintMismatch uncheckedTranscript noClaim recompute := by
  intro missing
  intro fail_closed
  exact ay_ucsw_conj_intro
    (AyUCSWConj noClaim recompute)
    (AyUCSWDisj missingParentAcrossWindow
      (AyUCSWDisj droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript))))
    fail_closed
    (ay_ucsw_disj_left missingParentAcrossWindow
      (AyUCSWDisj droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript)))
      missing)

theorem ay_ucsw_dropped_digest_forces_no_claim
    (missingParentAcrossWindow : Prop) (droppedDigest : Prop)
    (staleCheckpoint : Prop) (fingerprintMismatch : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    droppedDigest ->
    AyUCSWConj noClaim recompute ->
    AyUCSWBadWindow missingParentAcrossWindow droppedDigest staleCheckpoint
      fingerprintMismatch uncheckedTranscript noClaim recompute := by
  intro dropped
  intro fail_closed
  exact ay_ucsw_conj_intro
    (AyUCSWConj noClaim recompute)
    (AyUCSWDisj missingParentAcrossWindow
      (AyUCSWDisj droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript))))
    fail_closed
    (ay_ucsw_disj_right missingParentAcrossWindow
      (AyUCSWDisj droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript)))
      (ay_ucsw_disj_left droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript))
        dropped))

theorem ay_ucsw_stale_checkpoint_forces_no_claim
    (missingParentAcrossWindow : Prop) (droppedDigest : Prop)
    (staleCheckpoint : Prop) (fingerprintMismatch : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    staleCheckpoint ->
    AyUCSWConj noClaim recompute ->
    AyUCSWBadWindow missingParentAcrossWindow droppedDigest staleCheckpoint
      fingerprintMismatch uncheckedTranscript noClaim recompute := by
  intro stale
  intro fail_closed
  exact ay_ucsw_conj_intro
    (AyUCSWConj noClaim recompute)
    (AyUCSWDisj missingParentAcrossWindow
      (AyUCSWDisj droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript))))
    fail_closed
    (ay_ucsw_disj_right missingParentAcrossWindow
      (AyUCSWDisj droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript)))
      (ay_ucsw_disj_right droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript))
        (ay_ucsw_disj_left staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript)
          stale)))

theorem ay_ucsw_fingerprint_mismatch_forces_no_claim
    (missingParentAcrossWindow : Prop) (droppedDigest : Prop)
    (staleCheckpoint : Prop) (fingerprintMismatch : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    fingerprintMismatch ->
    AyUCSWConj noClaim recompute ->
    AyUCSWBadWindow missingParentAcrossWindow droppedDigest staleCheckpoint
      fingerprintMismatch uncheckedTranscript noClaim recompute := by
  intro mismatch
  intro fail_closed
  exact ay_ucsw_conj_intro
    (AyUCSWConj noClaim recompute)
    (AyUCSWDisj missingParentAcrossWindow
      (AyUCSWDisj droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript))))
    fail_closed
    (ay_ucsw_disj_right missingParentAcrossWindow
      (AyUCSWDisj droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript)))
      (ay_ucsw_disj_right droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript))
        (ay_ucsw_disj_right staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript)
          (ay_ucsw_disj_left fingerprintMismatch uncheckedTranscript
            mismatch))))

theorem ay_ucsw_unchecked_transcript_forces_no_claim
    (missingParentAcrossWindow : Prop) (droppedDigest : Prop)
    (staleCheckpoint : Prop) (fingerprintMismatch : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    uncheckedTranscript ->
    AyUCSWConj noClaim recompute ->
    AyUCSWBadWindow missingParentAcrossWindow droppedDigest staleCheckpoint
      fingerprintMismatch uncheckedTranscript noClaim recompute := by
  intro unchecked
  intro fail_closed
  exact ay_ucsw_conj_intro
    (AyUCSWConj noClaim recompute)
    (AyUCSWDisj missingParentAcrossWindow
      (AyUCSWDisj droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript))))
    fail_closed
    (ay_ucsw_disj_right missingParentAcrossWindow
      (AyUCSWDisj droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript)))
      (ay_ucsw_disj_right droppedDigest
        (AyUCSWDisj staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript))
        (ay_ucsw_disj_right staleCheckpoint
          (AyUCSWDisj fingerprintMismatch uncheckedTranscript)
          (ay_ucsw_disj_right fingerprintMismatch uncheckedTranscript
            unchecked))))

theorem ay_ucsw_unchecked_transcript_cannot_publish
    (missingParentAcrossWindow : Prop) (droppedDigest : Prop)
    (staleCheckpoint : Prop) (fingerprintMismatch : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUCSWBadWindow missingParentAcrossWindow droppedDigest staleCheckpoint
      fingerprintMismatch uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_ucsw_bad_window_cannot_publish missingParentAcrossWindow
    droppedDigest staleCheckpoint fingerprintMismatch uncheckedTranscript
    noClaim recompute originalUnsat bad
