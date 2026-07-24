-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded incremental proof append manifest soundness for ay sequential-main
-- SAT-COMP UNSAT checking. Propositions stand for append manifests, previous
-- proof digests, new chunk digests, parent coverage, root empty clauses,
-- checker transcripts, formula fingerprints, reconstruction evidence, and
-- fail-closed no-claim/recompute diagnostics.

def AyUIPAConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUIPADisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUIPAMap (source : Prop) (target : Prop) :=
  source -> target

def AyUIPAAppendManifest
    (appendManifest : Prop) (previousDigest : Prop)
    (appendedReplay : Prop) :=
  AyUIPAConj appendManifest
    (AyUIPAConj
      (AyUIPAMap appendManifest previousDigest)
      (AyUIPAMap previousDigest appendedReplay))

def AyUIPANewChunkDigest
    (appendedReplay : Prop) (newChunkDigest : Prop)
    (chunkDigestAccepted : Prop) :=
  AyUIPAConj
    (AyUIPAMap appendedReplay newChunkDigest)
    (AyUIPAMap newChunkDigest chunkDigestAccepted)

def AyUIPAParentCoverage
    (appendedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :=
  AyUIPAConj
    (AyUIPAMap appendedReplay parentCoverage)
    (AyUIPAMap parentCoverage rootEmptyClause)

def AyUIPACheckerTranscript
    (appendedReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :=
  AyUIPAConj
    (AyUIPAMap appendedReplay checkerTranscript)
    (AyUIPAMap checkerTranscript transcriptAccepted)

def AyUIPAFormulaFingerprint
    (appendedReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUIPAConj
    (AyUIPAMap appendedReplay formulaFingerprint)
    (AyUIPAMap formulaFingerprint fingerprintAccepted)

def AyUIPAReconstruction
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUIPAConj reconstructionEvidence
    (AyUIPAConj
      (AyUIPAMap rootEmptyClause visibleUnsat)
      (AyUIPAMap visibleUnsat originalUnsat))

def AyUIPAAcceptedEvidence
    (appendManifest : Prop) (previousDigest : Prop)
    (appendedReplay : Prop) (newChunkDigest : Prop)
    (chunkDigestAccepted : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUIPAConj
    (AyUIPAAppendManifest appendManifest previousDigest appendedReplay)
    (AyUIPAConj
      (AyUIPANewChunkDigest appendedReplay newChunkDigest
        chunkDigestAccepted)
      (AyUIPAConj
        (AyUIPAParentCoverage appendedReplay parentCoverage rootEmptyClause)
        (AyUIPAConj
          (AyUIPACheckerTranscript appendedReplay checkerTranscript
            transcriptAccepted)
          (AyUIPAConj
            (AyUIPAFormulaFingerprint appendedReplay formulaFingerprint
              fingerprintAccepted)
            (AyUIPAReconstruction rootEmptyClause reconstructionEvidence
              visibleUnsat originalUnsat)))))

def AyUIPAAcceptedAppend
    (appendManifest : Prop) (previousDigest : Prop)
    (appendedReplay : Prop) (newChunkDigest : Prop)
    (chunkDigestAccepted : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUIPAConj
    (AyUIPAAcceptedEvidence appendManifest previousDigest appendedReplay
      newChunkDigest chunkDigestAccepted parentCoverage rootEmptyClause
      checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat)
    originalUnsat

def AyUIPABadAppend
    (appendDrift : Prop) (previousDigestMismatch : Prop)
    (missingParent : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUIPAConj
    (AyUIPAConj noClaim recompute)
    (AyUIPADisj appendDrift
      (AyUIPADisj previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript))))

def AyUIPAPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUIPADisj noClaim originalUnsat

theorem ay_uipa_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUIPAConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_uipa_conj_left
    (p : Prop) (q : Prop) :
    AyUIPAConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_uipa_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUIPADisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_uipa_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUIPADisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_uipa_append_manifest
    (appendManifest : Prop) (previousDigest : Prop)
    (appendedReplay : Prop) :
    AyUIPAAppendManifest appendManifest previousDigest appendedReplay ->
    appendManifest := by
  intro manifest
  exact manifest appendManifest
    (fun append_manifest _tail => append_manifest)

theorem ay_uipa_previous_digest
    (appendManifest : Prop) (previousDigest : Prop)
    (appendedReplay : Prop) :
    AyUIPAAppendManifest appendManifest previousDigest appendedReplay ->
    previousDigest := by
  intro manifest
  exact manifest previousDigest
    (fun (append_manifest : appendManifest) tail =>
      tail previousDigest
        (fun manifest_to_previous _previous_to_replay =>
          manifest_to_previous append_manifest))

theorem ay_uipa_appended_replay
    (appendManifest : Prop) (previousDigest : Prop)
    (appendedReplay : Prop) :
    AyUIPAAppendManifest appendManifest previousDigest appendedReplay ->
    appendedReplay := by
  intro manifest
  exact manifest appendedReplay
    (fun (append_manifest : appendManifest) tail =>
      tail appendedReplay
        (fun manifest_to_previous previous_to_replay =>
          previous_to_replay (manifest_to_previous append_manifest)))

theorem ay_uipa_new_chunk_digest
    (appendedReplay : Prop) (newChunkDigest : Prop)
    (chunkDigestAccepted : Prop) :
    AyUIPANewChunkDigest appendedReplay newChunkDigest
      chunkDigestAccepted ->
    appendedReplay ->
    newChunkDigest := by
  intro digest
  exact digest (appendedReplay -> newChunkDigest)
    (fun replay_to_digest _digest_to_accept => replay_to_digest)

theorem ay_uipa_chunk_digest_accepted
    (appendedReplay : Prop) (newChunkDigest : Prop)
    (chunkDigestAccepted : Prop) :
    AyUIPANewChunkDigest appendedReplay newChunkDigest
      chunkDigestAccepted ->
    newChunkDigest ->
    chunkDigestAccepted := by
  intro digest
  exact digest (newChunkDigest -> chunkDigestAccepted)
    (fun _replay_to_digest digest_to_accept => digest_to_accept)

theorem ay_uipa_parent_coverage
    (appendedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :
    AyUIPAParentCoverage appendedReplay parentCoverage rootEmptyClause ->
    appendedReplay ->
    parentCoverage := by
  intro parents
  exact parents (appendedReplay -> parentCoverage)
    (fun replay_to_parent _parent_to_root => replay_to_parent)

theorem ay_uipa_root_empty_clause
    (appendedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :
    AyUIPAParentCoverage appendedReplay parentCoverage rootEmptyClause ->
    parentCoverage ->
    rootEmptyClause := by
  intro parents
  exact parents (parentCoverage -> rootEmptyClause)
    (fun _replay_to_parent parent_to_root => parent_to_root)

theorem ay_uipa_checker_transcript
    (appendedReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUIPACheckerTranscript appendedReplay checkerTranscript
      transcriptAccepted ->
    appendedReplay ->
    checkerTranscript := by
  intro transcript
  exact transcript (appendedReplay -> checkerTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_uipa_transcript_accepted
    (appendedReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUIPACheckerTranscript appendedReplay checkerTranscript
      transcriptAccepted ->
    checkerTranscript ->
    transcriptAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> transcriptAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_uipa_formula_fingerprint
    (appendedReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUIPAFormulaFingerprint appendedReplay formulaFingerprint
      fingerprintAccepted ->
    appendedReplay ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (appendedReplay -> formulaFingerprint)
    (fun replay_to_fingerprint _fingerprint_to_accept =>
      replay_to_fingerprint)

theorem ay_uipa_fingerprint_accepted
    (appendedReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUIPAFormulaFingerprint appendedReplay formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _replay_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_uipa_reconstruction_evidence
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUIPAReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_uipa_conj_left reconstructionEvidence
    (AyUIPAConj
      (AyUIPAMap rootEmptyClause visibleUnsat)
      (AyUIPAMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_uipa_visible_unsat_from_root
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUIPAReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    rootEmptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (rootEmptyClause -> visibleUnsat)
    (fun _evidence tail =>
      tail (rootEmptyClause -> visibleUnsat)
        (fun root_to_visible _visible_to_original => root_to_visible))

theorem ay_uipa_original_unsat_from_visible
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUIPAReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _evidence tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _root_to_visible visible_to_original => visible_to_original))

theorem ay_uipa_accepted_evidence
    (appendManifest : Prop) (previousDigest : Prop)
    (appendedReplay : Prop) (newChunkDigest : Prop)
    (chunkDigestAccepted : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUIPAAcceptedAppend appendManifest previousDigest appendedReplay
      newChunkDigest chunkDigestAccepted parentCoverage rootEmptyClause
      checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat ->
    AyUIPAAcceptedEvidence appendManifest previousDigest appendedReplay
      newChunkDigest chunkDigestAccepted parentCoverage rootEmptyClause
      checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat := by
  intro accepted
  exact ay_uipa_conj_left
    (AyUIPAAcceptedEvidence appendManifest previousDigest appendedReplay
      newChunkDigest chunkDigestAccepted parentCoverage rootEmptyClause
      checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_uipa_accepted_original_unsat
    (appendManifest : Prop) (previousDigest : Prop)
    (appendedReplay : Prop) (newChunkDigest : Prop)
    (chunkDigestAccepted : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUIPAAcceptedAppend appendManifest previousDigest appendedReplay
      newChunkDigest chunkDigestAccepted parentCoverage rootEmptyClause
      checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_uipa_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUIPAPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_uipa_disj_right noClaim originalUnsat unsat

theorem ay_uipa_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUIPAPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_uipa_disj_left noClaim originalUnsat no_claim

theorem ay_uipa_accepted_append_publish_sound
    (appendManifest : Prop) (previousDigest : Prop)
    (appendedReplay : Prop) (newChunkDigest : Prop)
    (chunkDigestAccepted : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUIPAAcceptedAppend appendManifest previousDigest appendedReplay
      newChunkDigest chunkDigestAccepted parentCoverage rootEmptyClause
      checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat ->
    AyUIPAPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_uipa_public_unsat_report noClaim originalUnsat
    (ay_uipa_accepted_original_unsat appendManifest previousDigest
      appendedReplay newChunkDigest chunkDigestAccepted parentCoverage
      rootEmptyClause checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat
      accepted)

theorem ay_uipa_bad_append_no_claim
    (appendDrift : Prop) (previousDigestMismatch : Prop)
    (missingParent : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUIPABadAppend appendDrift previousDigestMismatch missingParent
      staleFingerprint uncheckedTranscript noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_uipa_conj_left noClaim recompute fail_closed)

theorem ay_uipa_bad_append_recompute
    (appendDrift : Prop) (previousDigestMismatch : Prop)
    (missingParent : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUIPABadAppend appendDrift previousDigestMismatch missingParent
      staleFingerprint uncheckedTranscript noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_uipa_bad_append_public_no_claim
    (appendDrift : Prop) (previousDigestMismatch : Prop)
    (missingParent : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUIPABadAppend appendDrift previousDigestMismatch missingParent
      staleFingerprint uncheckedTranscript noClaim recompute ->
    AyUIPAPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_uipa_public_no_claim_report noClaim originalUnsat
    (ay_uipa_bad_append_no_claim appendDrift previousDigestMismatch
      missingParent staleFingerprint uncheckedTranscript noClaim recompute
      bad)

theorem ay_uipa_bad_append_cannot_publish
    (appendDrift : Prop) (previousDigestMismatch : Prop)
    (missingParent : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUIPABadAppend appendDrift previousDigestMismatch missingParent
      staleFingerprint uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_uipa_bad_append_no_claim appendDrift previousDigestMismatch
      missingParent staleFingerprint uncheckedTranscript noClaim recompute
      bad)
    unsat

theorem ay_uipa_append_drift_forces_no_claim
    (appendDrift : Prop) (previousDigestMismatch : Prop)
    (missingParent : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    appendDrift ->
    AyUIPAConj noClaim recompute ->
    AyUIPABadAppend appendDrift previousDigestMismatch missingParent
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro drift
  intro fail_closed
  exact ay_uipa_conj_intro
    (AyUIPAConj noClaim recompute)
    (AyUIPADisj appendDrift
      (AyUIPADisj previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_uipa_disj_left appendDrift
      (AyUIPADisj previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript)))
      drift)

theorem ay_uipa_previous_digest_mismatch_forces_no_claim
    (appendDrift : Prop) (previousDigestMismatch : Prop)
    (missingParent : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    previousDigestMismatch ->
    AyUIPAConj noClaim recompute ->
    AyUIPABadAppend appendDrift previousDigestMismatch missingParent
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro mismatch
  intro fail_closed
  exact ay_uipa_conj_intro
    (AyUIPAConj noClaim recompute)
    (AyUIPADisj appendDrift
      (AyUIPADisj previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_uipa_disj_right appendDrift
      (AyUIPADisj previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript)))
      (ay_uipa_disj_left previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript))
        mismatch))

theorem ay_uipa_missing_parent_forces_no_claim
    (appendDrift : Prop) (previousDigestMismatch : Prop)
    (missingParent : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    missingParent ->
    AyUIPAConj noClaim recompute ->
    AyUIPABadAppend appendDrift previousDigestMismatch missingParent
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro missing
  intro fail_closed
  exact ay_uipa_conj_intro
    (AyUIPAConj noClaim recompute)
    (AyUIPADisj appendDrift
      (AyUIPADisj previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_uipa_disj_right appendDrift
      (AyUIPADisj previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript)))
      (ay_uipa_disj_right previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript))
        (ay_uipa_disj_left missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript)
          missing)))

theorem ay_uipa_stale_fingerprint_forces_no_claim
    (appendDrift : Prop) (previousDigestMismatch : Prop)
    (missingParent : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    staleFingerprint ->
    AyUIPAConj noClaim recompute ->
    AyUIPABadAppend appendDrift previousDigestMismatch missingParent
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro stale
  intro fail_closed
  exact ay_uipa_conj_intro
    (AyUIPAConj noClaim recompute)
    (AyUIPADisj appendDrift
      (AyUIPADisj previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_uipa_disj_right appendDrift
      (AyUIPADisj previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript)))
      (ay_uipa_disj_right previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript))
        (ay_uipa_disj_right missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript)
          (ay_uipa_disj_left staleFingerprint uncheckedTranscript stale))))

theorem ay_uipa_unchecked_transcript_forces_no_claim
    (appendDrift : Prop) (previousDigestMismatch : Prop)
    (missingParent : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    uncheckedTranscript ->
    AyUIPAConj noClaim recompute ->
    AyUIPABadAppend appendDrift previousDigestMismatch missingParent
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro unchecked
  intro fail_closed
  exact ay_uipa_conj_intro
    (AyUIPAConj noClaim recompute)
    (AyUIPADisj appendDrift
      (AyUIPADisj previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_uipa_disj_right appendDrift
      (AyUIPADisj previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript)))
      (ay_uipa_disj_right previousDigestMismatch
        (AyUIPADisj missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript))
        (ay_uipa_disj_right missingParent
          (AyUIPADisj staleFingerprint uncheckedTranscript)
          (ay_uipa_disj_right staleFingerprint uncheckedTranscript
            unchecked))))

theorem ay_uipa_unchecked_transcript_cannot_publish
    (appendDrift : Prop) (previousDigestMismatch : Prop)
    (missingParent : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUIPABadAppend appendDrift previousDigestMismatch missingParent
      staleFingerprint uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_uipa_bad_append_cannot_publish appendDrift
    previousDigestMismatch missingParent staleFingerprint uncheckedTranscript
    noClaim recompute originalUnsat bad
