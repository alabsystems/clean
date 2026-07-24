-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded proof-index compression manifest soundness for ay sequential-main
-- SAT-COMP UNSAT checking. Propositions stand for compressed proof indexes,
-- index manifests, decompression transcripts, step maps, parent coverage,
-- root empty clauses, checker transcripts, formula fingerprints,
-- reconstruction evidence, and fail-closed no-claim/recompute diagnostics.

def AyUPICConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUPICDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUPICMap (source : Prop) (target : Prop) :=
  source -> target

def AyUPICIndexManifest
    (compressedIndex : Prop) (indexManifest : Prop)
    (indexedReplay : Prop) :=
  AyUPICConj compressedIndex
    (AyUPICConj
      (AyUPICMap compressedIndex indexManifest)
      (AyUPICMap indexManifest indexedReplay))

def AyUPICDecompressionTranscript
    (indexedReplay : Prop) (decompressionTranscript : Prop)
    (decompressionAccepted : Prop) :=
  AyUPICConj
    (AyUPICMap indexedReplay decompressionTranscript)
    (AyUPICMap decompressionTranscript decompressionAccepted)

def AyUPICStepMap
    (indexedReplay : Prop) (stepMap : Prop)
    (stepMapAccepted : Prop) :=
  AyUPICConj
    (AyUPICMap indexedReplay stepMap)
    (AyUPICMap stepMap stepMapAccepted)

def AyUPICParentCoverage
    (indexedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :=
  AyUPICConj
    (AyUPICMap indexedReplay parentCoverage)
    (AyUPICMap parentCoverage rootEmptyClause)

def AyUPICCheckerTranscript
    (indexedReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :=
  AyUPICConj
    (AyUPICMap indexedReplay checkerTranscript)
    (AyUPICMap checkerTranscript transcriptAccepted)

def AyUPICFormulaFingerprint
    (indexedReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUPICConj
    (AyUPICMap indexedReplay formulaFingerprint)
    (AyUPICMap formulaFingerprint fingerprintAccepted)

def AyUPICReconstruction
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPICConj reconstructionEvidence
    (AyUPICConj
      (AyUPICMap rootEmptyClause visibleUnsat)
      (AyUPICMap visibleUnsat originalUnsat))

def AyUPICAcceptedEvidence
    (compressedIndex : Prop) (indexManifest : Prop)
    (indexedReplay : Prop) (decompressionTranscript : Prop)
    (decompressionAccepted : Prop) (stepMap : Prop)
    (stepMapAccepted : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPICConj
    (AyUPICIndexManifest compressedIndex indexManifest indexedReplay)
    (AyUPICConj
      (AyUPICDecompressionTranscript indexedReplay decompressionTranscript
        decompressionAccepted)
      (AyUPICConj
        (AyUPICStepMap indexedReplay stepMap stepMapAccepted)
        (AyUPICConj
          (AyUPICParentCoverage indexedReplay parentCoverage rootEmptyClause)
          (AyUPICConj
            (AyUPICCheckerTranscript indexedReplay checkerTranscript
              transcriptAccepted)
            (AyUPICConj
              (AyUPICFormulaFingerprint indexedReplay formulaFingerprint
                fingerprintAccepted)
              (AyUPICReconstruction rootEmptyClause reconstructionEvidence
                visibleUnsat originalUnsat)))))))

def AyUPICAcceptedIndex
    (compressedIndex : Prop) (indexManifest : Prop)
    (indexedReplay : Prop) (decompressionTranscript : Prop)
    (decompressionAccepted : Prop) (stepMap : Prop)
    (stepMapAccepted : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUPICConj
    (AyUPICAcceptedEvidence compressedIndex indexManifest indexedReplay
      decompressionTranscript decompressionAccepted stepMap stepMapAccepted
      parentCoverage rootEmptyClause checkerTranscript transcriptAccepted
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat)
    originalUnsat

def AyUPICBadIndex
    (decompressionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUPICConj
    (AyUPICConj noClaim recompute)
    (AyUPICDisj decompressionDrift
      (AyUPICDisj missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript))))

def AyUPICPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUPICDisj noClaim originalUnsat

theorem ay_upic_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUPICConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_upic_conj_left
    (p : Prop) (q : Prop) :
    AyUPICConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_upic_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUPICDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_upic_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUPICDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_upic_compressed_index
    (compressedIndex : Prop) (indexManifest : Prop)
    (indexedReplay : Prop) :
    AyUPICIndexManifest compressedIndex indexManifest indexedReplay ->
    compressedIndex := by
  intro manifest
  exact manifest compressedIndex
    (fun index _tail => index)

theorem ay_upic_index_manifest
    (compressedIndex : Prop) (indexManifest : Prop)
    (indexedReplay : Prop) :
    AyUPICIndexManifest compressedIndex indexManifest indexedReplay ->
    indexManifest := by
  intro manifest
  exact manifest indexManifest
    (fun (index : compressedIndex) tail =>
      tail indexManifest
        (fun index_to_manifest _manifest_to_replay =>
          index_to_manifest index))

theorem ay_upic_indexed_replay
    (compressedIndex : Prop) (indexManifest : Prop)
    (indexedReplay : Prop) :
    AyUPICIndexManifest compressedIndex indexManifest indexedReplay ->
    indexedReplay := by
  intro manifest
  exact manifest indexedReplay
    (fun (index : compressedIndex) tail =>
      tail indexedReplay
        (fun index_to_manifest manifest_to_replay =>
          manifest_to_replay (index_to_manifest index)))

theorem ay_upic_decompression_transcript
    (indexedReplay : Prop) (decompressionTranscript : Prop)
    (decompressionAccepted : Prop) :
    AyUPICDecompressionTranscript indexedReplay decompressionTranscript
      decompressionAccepted ->
    indexedReplay ->
    decompressionTranscript := by
  intro transcript
  exact transcript (indexedReplay -> decompressionTranscript)
    (fun replay_to_decompression _decompression_to_accept =>
      replay_to_decompression)

theorem ay_upic_decompression_accepted
    (indexedReplay : Prop) (decompressionTranscript : Prop)
    (decompressionAccepted : Prop) :
    AyUPICDecompressionTranscript indexedReplay decompressionTranscript
      decompressionAccepted ->
    decompressionTranscript ->
    decompressionAccepted := by
  intro transcript
  exact transcript (decompressionTranscript -> decompressionAccepted)
    (fun _replay_to_decompression decompression_to_accept =>
      decompression_to_accept)

theorem ay_upic_step_map
    (indexedReplay : Prop) (stepMap : Prop) (stepMapAccepted : Prop) :
    AyUPICStepMap indexedReplay stepMap stepMapAccepted ->
    indexedReplay ->
    stepMap := by
  intro step
  exact step (indexedReplay -> stepMap)
    (fun replay_to_step _step_to_accept => replay_to_step)

theorem ay_upic_step_map_accepted
    (indexedReplay : Prop) (stepMap : Prop) (stepMapAccepted : Prop) :
    AyUPICStepMap indexedReplay stepMap stepMapAccepted ->
    stepMap ->
    stepMapAccepted := by
  intro step
  exact step (stepMap -> stepMapAccepted)
    (fun _replay_to_step step_to_accept => step_to_accept)

theorem ay_upic_parent_coverage
    (indexedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :
    AyUPICParentCoverage indexedReplay parentCoverage rootEmptyClause ->
    indexedReplay ->
    parentCoverage := by
  intro parents
  exact parents (indexedReplay -> parentCoverage)
    (fun replay_to_parent _parent_to_root => replay_to_parent)

theorem ay_upic_root_empty_clause
    (indexedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :
    AyUPICParentCoverage indexedReplay parentCoverage rootEmptyClause ->
    parentCoverage ->
    rootEmptyClause := by
  intro parents
  exact parents (parentCoverage -> rootEmptyClause)
    (fun _replay_to_parent parent_to_root => parent_to_root)

theorem ay_upic_checker_transcript
    (indexedReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUPICCheckerTranscript indexedReplay checkerTranscript
      transcriptAccepted ->
    indexedReplay ->
    checkerTranscript := by
  intro transcript
  exact transcript (indexedReplay -> checkerTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_upic_transcript_accepted
    (indexedReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUPICCheckerTranscript indexedReplay checkerTranscript
      transcriptAccepted ->
    checkerTranscript ->
    transcriptAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> transcriptAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_upic_formula_fingerprint
    (indexedReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUPICFormulaFingerprint indexedReplay formulaFingerprint
      fingerprintAccepted ->
    indexedReplay ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (indexedReplay -> formulaFingerprint)
    (fun replay_to_fingerprint _fingerprint_to_accept =>
      replay_to_fingerprint)

theorem ay_upic_fingerprint_accepted
    (indexedReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUPICFormulaFingerprint indexedReplay formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _replay_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_upic_reconstruction_evidence
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPICReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_upic_conj_left reconstructionEvidence
    (AyUPICConj
      (AyUPICMap rootEmptyClause visibleUnsat)
      (AyUPICMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_upic_visible_unsat_from_root
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPICReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    rootEmptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (rootEmptyClause -> visibleUnsat)
    (fun _evidence tail =>
      tail (rootEmptyClause -> visibleUnsat)
        (fun root_to_visible _visible_to_original => root_to_visible))

theorem ay_upic_original_unsat_from_visible
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPICReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _evidence tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _root_to_visible visible_to_original => visible_to_original))

theorem ay_upic_accepted_evidence
    (compressedIndex : Prop) (indexManifest : Prop)
    (indexedReplay : Prop) (decompressionTranscript : Prop)
    (decompressionAccepted : Prop) (stepMap : Prop)
    (stepMapAccepted : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPICAcceptedIndex compressedIndex indexManifest indexedReplay
      decompressionTranscript decompressionAccepted stepMap stepMapAccepted
      parentCoverage rootEmptyClause checkerTranscript transcriptAccepted
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat ->
    AyUPICAcceptedEvidence compressedIndex indexManifest indexedReplay
      decompressionTranscript decompressionAccepted stepMap stepMapAccepted
      parentCoverage rootEmptyClause checkerTranscript transcriptAccepted
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat := by
  intro accepted
  exact ay_upic_conj_left
    (AyUPICAcceptedEvidence compressedIndex indexManifest indexedReplay
      decompressionTranscript decompressionAccepted stepMap stepMapAccepted
      parentCoverage rootEmptyClause checkerTranscript transcriptAccepted
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_upic_accepted_original_unsat
    (compressedIndex : Prop) (indexManifest : Prop)
    (indexedReplay : Prop) (decompressionTranscript : Prop)
    (decompressionAccepted : Prop) (stepMap : Prop)
    (stepMapAccepted : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUPICAcceptedIndex compressedIndex indexManifest indexedReplay
      decompressionTranscript decompressionAccepted stepMap stepMapAccepted
      parentCoverage rootEmptyClause checkerTranscript transcriptAccepted
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_upic_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUPICPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_upic_disj_right noClaim originalUnsat unsat

theorem ay_upic_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUPICPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_upic_disj_left noClaim originalUnsat no_claim

theorem ay_upic_accepted_index_publish_sound
    (compressedIndex : Prop) (indexManifest : Prop)
    (indexedReplay : Prop) (decompressionTranscript : Prop)
    (decompressionAccepted : Prop) (stepMap : Prop)
    (stepMapAccepted : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUPICAcceptedIndex compressedIndex indexManifest indexedReplay
      decompressionTranscript decompressionAccepted stepMap stepMapAccepted
      parentCoverage rootEmptyClause checkerTranscript transcriptAccepted
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat ->
    AyUPICPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_upic_public_unsat_report noClaim originalUnsat
    (ay_upic_accepted_original_unsat compressedIndex indexManifest
      indexedReplay decompressionTranscript decompressionAccepted stepMap
      stepMapAccepted parentCoverage rootEmptyClause checkerTranscript
      transcriptAccepted formulaFingerprint fingerprintAccepted
      reconstructionEvidence visibleUnsat originalUnsat accepted)

theorem ay_upic_bad_index_no_claim
    (decompressionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPICBadIndex decompressionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_upic_conj_left noClaim recompute fail_closed)

theorem ay_upic_bad_index_recompute
    (decompressionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUPICBadIndex decompressionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_upic_bad_index_public_no_claim
    (decompressionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUPICBadIndex decompressionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    AyUPICPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_upic_public_no_claim_report noClaim originalUnsat
    (ay_upic_bad_index_no_claim decompressionDrift missingStepMap
      parentMismatch staleFingerprint uncheckedTranscript noClaim recompute
      bad)

theorem ay_upic_bad_index_cannot_publish
    (decompressionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUPICBadIndex decompressionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_upic_bad_index_no_claim decompressionDrift missingStepMap
      parentMismatch staleFingerprint uncheckedTranscript noClaim recompute
      bad)
    unsat

theorem ay_upic_decompression_drift_forces_no_claim
    (decompressionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    decompressionDrift ->
    AyUPICConj noClaim recompute ->
    AyUPICBadIndex decompressionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro drift
  intro fail_closed
  exact ay_upic_conj_intro
    (AyUPICConj noClaim recompute)
    (AyUPICDisj decompressionDrift
      (AyUPICDisj missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_upic_disj_left decompressionDrift
      (AyUPICDisj missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript)))
      drift)

theorem ay_upic_missing_step_map_forces_no_claim
    (decompressionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    missingStepMap ->
    AyUPICConj noClaim recompute ->
    AyUPICBadIndex decompressionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro missing
  intro fail_closed
  exact ay_upic_conj_intro
    (AyUPICConj noClaim recompute)
    (AyUPICDisj decompressionDrift
      (AyUPICDisj missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_upic_disj_right decompressionDrift
      (AyUPICDisj missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript)))
      (ay_upic_disj_left missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript))
        missing))

theorem ay_upic_parent_mismatch_forces_no_claim
    (decompressionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    parentMismatch ->
    AyUPICConj noClaim recompute ->
    AyUPICBadIndex decompressionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro mismatch
  intro fail_closed
  exact ay_upic_conj_intro
    (AyUPICConj noClaim recompute)
    (AyUPICDisj decompressionDrift
      (AyUPICDisj missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_upic_disj_right decompressionDrift
      (AyUPICDisj missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript)))
      (ay_upic_disj_right missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript))
        (ay_upic_disj_left parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript)
          mismatch)))

theorem ay_upic_stale_fingerprint_forces_no_claim
    (decompressionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    staleFingerprint ->
    AyUPICConj noClaim recompute ->
    AyUPICBadIndex decompressionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro stale
  intro fail_closed
  exact ay_upic_conj_intro
    (AyUPICConj noClaim recompute)
    (AyUPICDisj decompressionDrift
      (AyUPICDisj missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_upic_disj_right decompressionDrift
      (AyUPICDisj missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript)))
      (ay_upic_disj_right missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript))
        (ay_upic_disj_right parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript)
          (ay_upic_disj_left staleFingerprint uncheckedTranscript stale))))

theorem ay_upic_unchecked_transcript_forces_no_claim
    (decompressionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    uncheckedTranscript ->
    AyUPICConj noClaim recompute ->
    AyUPICBadIndex decompressionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro unchecked
  intro fail_closed
  exact ay_upic_conj_intro
    (AyUPICConj noClaim recompute)
    (AyUPICDisj decompressionDrift
      (AyUPICDisj missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_upic_disj_right decompressionDrift
      (AyUPICDisj missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript)))
      (ay_upic_disj_right missingStepMap
        (AyUPICDisj parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript))
        (ay_upic_disj_right parentMismatch
          (AyUPICDisj staleFingerprint uncheckedTranscript)
          (ay_upic_disj_right staleFingerprint uncheckedTranscript
            unchecked))))

theorem ay_upic_unchecked_transcript_cannot_publish
    (decompressionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUPICBadIndex decompressionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_upic_bad_index_cannot_publish decompressionDrift missingStepMap
    parentMismatch staleFingerprint uncheckedTranscript noClaim recompute
    originalUnsat bad
