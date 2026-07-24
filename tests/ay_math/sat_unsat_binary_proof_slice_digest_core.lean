-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded binary proof-slice digest soundness for ay sequential-main
-- SAT-COMP UNSAT checking. Propositions stand for compact binary proof slices,
-- slice digests, parent coverage, root empty clauses, checker transcripts,
-- formula fingerprints, chunk manifests, reconstruction evidence, and
-- fail-closed no-claim/recompute diagnostics.

def AyUBPSConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUBPSDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUBPSMap (source : Prop) (target : Prop) :=
  source -> target

def AyUBPSSliceDigest
    (binarySlice : Prop) (sliceDigest : Prop)
    (sliceReplay : Prop) :=
  AyUBPSConj binarySlice
    (AyUBPSConj
      (AyUBPSMap binarySlice sliceDigest)
      (AyUBPSMap sliceDigest sliceReplay))

def AyUBPSParentCoverage
    (sliceReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :=
  AyUBPSConj
    (AyUBPSMap sliceReplay parentCoverage)
    (AyUBPSMap parentCoverage rootEmptyClause)

def AyUBPSCheckerTranscript
    (sliceReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :=
  AyUBPSConj
    (AyUBPSMap sliceReplay checkerTranscript)
    (AyUBPSMap checkerTranscript transcriptAccepted)

def AyUBPSFormulaFingerprint
    (sliceReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUBPSConj
    (AyUBPSMap sliceReplay formulaFingerprint)
    (AyUBPSMap formulaFingerprint fingerprintAccepted)

def AyUBPSChunkManifest
    (sliceReplay : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) :=
  AyUBPSConj
    (AyUBPSMap sliceReplay chunkManifest)
    (AyUBPSMap chunkManifest manifestAccepted)

def AyUBPSReconstruction
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUBPSConj reconstructionEvidence
    (AyUBPSConj
      (AyUBPSMap rootEmptyClause visibleUnsat)
      (AyUBPSMap visibleUnsat originalUnsat))

def AyUBPSAcceptedEvidence
    (binarySlice : Prop) (sliceDigest : Prop)
    (sliceReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUBPSConj
    (AyUBPSSliceDigest binarySlice sliceDigest sliceReplay)
    (AyUBPSConj
      (AyUBPSParentCoverage sliceReplay parentCoverage rootEmptyClause)
      (AyUBPSConj
        (AyUBPSCheckerTranscript sliceReplay checkerTranscript
          transcriptAccepted)
        (AyUBPSConj
          (AyUBPSFormulaFingerprint sliceReplay formulaFingerprint
            fingerprintAccepted)
          (AyUBPSConj
            (AyUBPSChunkManifest sliceReplay chunkManifest manifestAccepted)
            (AyUBPSReconstruction rootEmptyClause reconstructionEvidence
              visibleUnsat originalUnsat)))))

def AyUBPSAcceptedSlice
    (binarySlice : Prop) (sliceDigest : Prop)
    (sliceReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUBPSConj
    (AyUBPSAcceptedEvidence binarySlice sliceDigest sliceReplay
      parentCoverage rootEmptyClause checkerTranscript transcriptAccepted
      formulaFingerprint fingerprintAccepted chunkManifest manifestAccepted
      reconstructionEvidence visibleUnsat originalUnsat)
    originalUnsat

def AyUBPSBadSlice
    (corruptSlice : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUBPSConj
    (AyUBPSConj noClaim recompute)
    (AyUBPSDisj corruptSlice
      (AyUBPSDisj missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript))))

def AyUBPSPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUBPSDisj noClaim originalUnsat

theorem ay_ubps_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUBPSConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ubps_conj_left
    (p : Prop) (q : Prop) :
    AyUBPSConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ubps_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUBPSDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ubps_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUBPSDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ubps_binary_slice
    (binarySlice : Prop) (sliceDigest : Prop)
    (sliceReplay : Prop) :
    AyUBPSSliceDigest binarySlice sliceDigest sliceReplay ->
    binarySlice := by
  intro slice
  exact slice binarySlice
    (fun binary _tail => binary)

theorem ay_ubps_slice_digest
    (binarySlice : Prop) (sliceDigest : Prop)
    (sliceReplay : Prop) :
    AyUBPSSliceDigest binarySlice sliceDigest sliceReplay ->
    sliceDigest := by
  intro slice
  exact slice sliceDigest
    (fun (binary : binarySlice) tail =>
      tail sliceDigest
        (fun binary_to_digest _digest_to_replay =>
          binary_to_digest binary))

theorem ay_ubps_slice_replay
    (binarySlice : Prop) (sliceDigest : Prop)
    (sliceReplay : Prop) :
    AyUBPSSliceDigest binarySlice sliceDigest sliceReplay ->
    sliceReplay := by
  intro slice
  exact slice sliceReplay
    (fun (binary : binarySlice) tail =>
      tail sliceReplay
        (fun binary_to_digest digest_to_replay =>
          digest_to_replay (binary_to_digest binary)))

theorem ay_ubps_parent_coverage
    (sliceReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :
    AyUBPSParentCoverage sliceReplay parentCoverage rootEmptyClause ->
    sliceReplay ->
    parentCoverage := by
  intro parents
  exact parents (sliceReplay -> parentCoverage)
    (fun replay_to_parent _parent_to_root => replay_to_parent)

theorem ay_ubps_root_empty_clause
    (sliceReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :
    AyUBPSParentCoverage sliceReplay parentCoverage rootEmptyClause ->
    parentCoverage ->
    rootEmptyClause := by
  intro parents
  exact parents (parentCoverage -> rootEmptyClause)
    (fun _replay_to_parent parent_to_root => parent_to_root)

theorem ay_ubps_checker_transcript
    (sliceReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUBPSCheckerTranscript sliceReplay checkerTranscript
      transcriptAccepted ->
    sliceReplay ->
    checkerTranscript := by
  intro transcript
  exact transcript (sliceReplay -> checkerTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_ubps_transcript_accepted
    (sliceReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUBPSCheckerTranscript sliceReplay checkerTranscript
      transcriptAccepted ->
    checkerTranscript ->
    transcriptAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> transcriptAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_ubps_formula_fingerprint
    (sliceReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUBPSFormulaFingerprint sliceReplay formulaFingerprint
      fingerprintAccepted ->
    sliceReplay ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (sliceReplay -> formulaFingerprint)
    (fun replay_to_fingerprint _fingerprint_to_accept =>
      replay_to_fingerprint)

theorem ay_ubps_fingerprint_accepted
    (sliceReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUBPSFormulaFingerprint sliceReplay formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _replay_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_ubps_chunk_manifest
    (sliceReplay : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) :
    AyUBPSChunkManifest sliceReplay chunkManifest manifestAccepted ->
    sliceReplay ->
    chunkManifest := by
  intro manifest
  exact manifest (sliceReplay -> chunkManifest)
    (fun replay_to_manifest _manifest_to_accept => replay_to_manifest)

theorem ay_ubps_manifest_accepted
    (sliceReplay : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) :
    AyUBPSChunkManifest sliceReplay chunkManifest manifestAccepted ->
    chunkManifest ->
    manifestAccepted := by
  intro manifest
  exact manifest (chunkManifest -> manifestAccepted)
    (fun _replay_to_manifest manifest_to_accept => manifest_to_accept)

theorem ay_ubps_reconstruction_evidence
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBPSReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_ubps_conj_left reconstructionEvidence
    (AyUBPSConj
      (AyUBPSMap rootEmptyClause visibleUnsat)
      (AyUBPSMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_ubps_visible_unsat_from_root
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBPSReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    rootEmptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (rootEmptyClause -> visibleUnsat)
    (fun _evidence tail =>
      tail (rootEmptyClause -> visibleUnsat)
        (fun root_to_visible _visible_to_original => root_to_visible))

theorem ay_ubps_original_unsat_from_visible
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBPSReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _evidence tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _root_to_visible visible_to_original => visible_to_original))

theorem ay_ubps_accepted_evidence
    (binarySlice : Prop) (sliceDigest : Prop)
    (sliceReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBPSAcceptedSlice binarySlice sliceDigest sliceReplay parentCoverage
      rootEmptyClause checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted chunkManifest manifestAccepted reconstructionEvidence
      visibleUnsat originalUnsat ->
    AyUBPSAcceptedEvidence binarySlice sliceDigest sliceReplay parentCoverage
      rootEmptyClause checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted chunkManifest manifestAccepted reconstructionEvidence
      visibleUnsat originalUnsat := by
  intro accepted
  exact ay_ubps_conj_left
    (AyUBPSAcceptedEvidence binarySlice sliceDigest sliceReplay
      parentCoverage rootEmptyClause checkerTranscript transcriptAccepted
      formulaFingerprint fingerprintAccepted chunkManifest manifestAccepted
      reconstructionEvidence visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_ubps_accepted_original_unsat
    (binarySlice : Prop) (sliceDigest : Prop)
    (sliceReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUBPSAcceptedSlice binarySlice sliceDigest sliceReplay parentCoverage
      rootEmptyClause checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted chunkManifest manifestAccepted reconstructionEvidence
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_ubps_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUBPSPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ubps_disj_right noClaim originalUnsat unsat

theorem ay_ubps_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUBPSPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ubps_disj_left noClaim originalUnsat no_claim

theorem ay_ubps_accepted_slice_publish_sound
    (binarySlice : Prop) (sliceDigest : Prop)
    (sliceReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (chunkManifest : Prop)
    (manifestAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUBPSAcceptedSlice binarySlice sliceDigest sliceReplay parentCoverage
      rootEmptyClause checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted chunkManifest manifestAccepted reconstructionEvidence
      visibleUnsat originalUnsat ->
    AyUBPSPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_ubps_public_unsat_report noClaim originalUnsat
    (ay_ubps_accepted_original_unsat binarySlice sliceDigest sliceReplay
      parentCoverage rootEmptyClause checkerTranscript transcriptAccepted
      formulaFingerprint fingerprintAccepted chunkManifest manifestAccepted
      reconstructionEvidence visibleUnsat originalUnsat accepted)

theorem ay_ubps_bad_slice_no_claim
    (corruptSlice : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUBPSBadSlice corruptSlice missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_ubps_conj_left noClaim recompute fail_closed)

theorem ay_ubps_bad_slice_recompute
    (corruptSlice : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUBPSBadSlice corruptSlice missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_ubps_bad_slice_public_no_claim
    (corruptSlice : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUBPSBadSlice corruptSlice missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute ->
    AyUBPSPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ubps_public_no_claim_report noClaim originalUnsat
    (ay_ubps_bad_slice_no_claim corruptSlice missingParent digestMismatch
      staleFingerprint uncheckedTranscript noClaim recompute bad)

theorem ay_ubps_bad_slice_cannot_publish
    (corruptSlice : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUBPSBadSlice corruptSlice missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_ubps_bad_slice_no_claim corruptSlice missingParent digestMismatch
      staleFingerprint uncheckedTranscript noClaim recompute bad)
    unsat

theorem ay_ubps_corrupt_slice_forces_no_claim
    (corruptSlice : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    corruptSlice ->
    AyUBPSConj noClaim recompute ->
    AyUBPSBadSlice corruptSlice missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute := by
  intro corrupt
  intro fail_closed
  exact ay_ubps_conj_intro
    (AyUBPSConj noClaim recompute)
    (AyUBPSDisj corruptSlice
      (AyUBPSDisj missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_ubps_disj_left corruptSlice
      (AyUBPSDisj missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript)))
      corrupt)

theorem ay_ubps_missing_parent_forces_no_claim
    (corruptSlice : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    missingParent ->
    AyUBPSConj noClaim recompute ->
    AyUBPSBadSlice corruptSlice missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute := by
  intro missing
  intro fail_closed
  exact ay_ubps_conj_intro
    (AyUBPSConj noClaim recompute)
    (AyUBPSDisj corruptSlice
      (AyUBPSDisj missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_ubps_disj_right corruptSlice
      (AyUBPSDisj missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript)))
      (ay_ubps_disj_left missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript))
        missing))

theorem ay_ubps_digest_mismatch_forces_no_claim
    (corruptSlice : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    digestMismatch ->
    AyUBPSConj noClaim recompute ->
    AyUBPSBadSlice corruptSlice missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute := by
  intro mismatch
  intro fail_closed
  exact ay_ubps_conj_intro
    (AyUBPSConj noClaim recompute)
    (AyUBPSDisj corruptSlice
      (AyUBPSDisj missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_ubps_disj_right corruptSlice
      (AyUBPSDisj missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript)))
      (ay_ubps_disj_right missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript))
        (ay_ubps_disj_left digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript)
          mismatch)))

theorem ay_ubps_stale_fingerprint_forces_no_claim
    (corruptSlice : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    staleFingerprint ->
    AyUBPSConj noClaim recompute ->
    AyUBPSBadSlice corruptSlice missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute := by
  intro stale
  intro fail_closed
  exact ay_ubps_conj_intro
    (AyUBPSConj noClaim recompute)
    (AyUBPSDisj corruptSlice
      (AyUBPSDisj missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_ubps_disj_right corruptSlice
      (AyUBPSDisj missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript)))
      (ay_ubps_disj_right missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript))
        (ay_ubps_disj_right digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript)
          (ay_ubps_disj_left staleFingerprint uncheckedTranscript stale))))

theorem ay_ubps_unchecked_transcript_forces_no_claim
    (corruptSlice : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    uncheckedTranscript ->
    AyUBPSConj noClaim recompute ->
    AyUBPSBadSlice corruptSlice missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute := by
  intro unchecked
  intro fail_closed
  exact ay_ubps_conj_intro
    (AyUBPSConj noClaim recompute)
    (AyUBPSDisj corruptSlice
      (AyUBPSDisj missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_ubps_disj_right corruptSlice
      (AyUBPSDisj missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript)))
      (ay_ubps_disj_right missingParent
        (AyUBPSDisj digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript))
        (ay_ubps_disj_right digestMismatch
          (AyUBPSDisj staleFingerprint uncheckedTranscript)
          (ay_ubps_disj_right staleFingerprint uncheckedTranscript
            unchecked))))

theorem ay_ubps_unchecked_transcript_cannot_publish
    (corruptSlice : Prop) (missingParent : Prop)
    (digestMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUBPSBadSlice corruptSlice missingParent digestMismatch staleFingerprint
      uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_ubps_bad_slice_cannot_publish corruptSlice missingParent
    digestMismatch staleFingerprint uncheckedTranscript noClaim recompute
    originalUnsat bad
