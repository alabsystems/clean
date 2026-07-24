-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded clause-ID renumbering manifest soundness for ay sequential-main
-- SAT-COMP UNSAT checking. Propositions stand for renumbering manifests,
-- inverse maps, parent coverage, root empty clauses, checker transcripts,
-- formula fingerprints, reconstruction evidence, and fail-closed
-- no-claim/recompute diagnostics.

def AyUCIRConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUCIRDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUCIRMap (source : Prop) (target : Prop) :=
  source -> target

def AyUCIRRenumberingManifest
    (renumberingManifest : Prop) (inverseMap : Prop)
    (renumberedReplay : Prop) :=
  AyUCIRConj renumberingManifest
    (AyUCIRConj
      (AyUCIRMap renumberingManifest inverseMap)
      (AyUCIRMap inverseMap renumberedReplay))

def AyUCIRParentCoverage
    (renumberedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :=
  AyUCIRConj
    (AyUCIRMap renumberedReplay parentCoverage)
    (AyUCIRMap parentCoverage rootEmptyClause)

def AyUCIRCheckerTranscript
    (renumberedReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :=
  AyUCIRConj
    (AyUCIRMap renumberedReplay checkerTranscript)
    (AyUCIRMap checkerTranscript transcriptAccepted)

def AyUCIRFormulaFingerprint
    (renumberedReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUCIRConj
    (AyUCIRMap renumberedReplay formulaFingerprint)
    (AyUCIRMap formulaFingerprint fingerprintAccepted)

def AyUCIRReconstruction
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCIRConj reconstructionEvidence
    (AyUCIRConj
      (AyUCIRMap rootEmptyClause visibleUnsat)
      (AyUCIRMap visibleUnsat originalUnsat))

def AyUCIRAcceptedEvidence
    (renumberingManifest : Prop) (inverseMap : Prop)
    (renumberedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCIRConj
    (AyUCIRRenumberingManifest renumberingManifest inverseMap
      renumberedReplay)
    (AyUCIRConj
      (AyUCIRParentCoverage renumberedReplay parentCoverage rootEmptyClause)
      (AyUCIRConj
        (AyUCIRCheckerTranscript renumberedReplay checkerTranscript
          transcriptAccepted)
        (AyUCIRConj
          (AyUCIRFormulaFingerprint renumberedReplay formulaFingerprint
            fingerprintAccepted)
          (AyUCIRReconstruction rootEmptyClause reconstructionEvidence
            visibleUnsat originalUnsat))))

def AyUCIRAcceptedRenumbering
    (renumberingManifest : Prop) (inverseMap : Prop)
    (renumberedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUCIRConj
    (AyUCIRAcceptedEvidence renumberingManifest inverseMap
      renumberedReplay parentCoverage rootEmptyClause checkerTranscript
      transcriptAccepted formulaFingerprint fingerprintAccepted
      reconstructionEvidence visibleUnsat originalUnsat)
    originalUnsat

def AyUCIRBadRenumbering
    (idDrift : Prop) (missingInverseMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUCIRConj
    (AyUCIRConj noClaim recompute)
    (AyUCIRDisj idDrift
      (AyUCIRDisj missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript))))

def AyUCIRPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUCIRDisj noClaim originalUnsat

theorem ay_ucir_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUCIRConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_ucir_conj_left
    (p : Prop) (q : Prop) :
    AyUCIRConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_ucir_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUCIRDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_ucir_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUCIRDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_ucir_renumbering_manifest
    (renumberingManifest : Prop) (inverseMap : Prop)
    (renumberedReplay : Prop) :
    AyUCIRRenumberingManifest renumberingManifest inverseMap
      renumberedReplay ->
    renumberingManifest := by
  intro manifest
  exact manifest renumberingManifest
    (fun renumbering _tail => renumbering)

theorem ay_ucir_inverse_map
    (renumberingManifest : Prop) (inverseMap : Prop)
    (renumberedReplay : Prop) :
    AyUCIRRenumberingManifest renumberingManifest inverseMap
      renumberedReplay ->
    inverseMap := by
  intro manifest
  exact manifest inverseMap
    (fun (renumbering : renumberingManifest) tail =>
      tail inverseMap
        (fun manifest_to_inverse _inverse_to_replay =>
          manifest_to_inverse renumbering))

theorem ay_ucir_renumbered_replay
    (renumberingManifest : Prop) (inverseMap : Prop)
    (renumberedReplay : Prop) :
    AyUCIRRenumberingManifest renumberingManifest inverseMap
      renumberedReplay ->
    renumberedReplay := by
  intro manifest
  exact manifest renumberedReplay
    (fun (renumbering : renumberingManifest) tail =>
      tail renumberedReplay
        (fun manifest_to_inverse inverse_to_replay =>
          inverse_to_replay (manifest_to_inverse renumbering)))

theorem ay_ucir_parent_coverage
    (renumberedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :
    AyUCIRParentCoverage renumberedReplay parentCoverage rootEmptyClause ->
    renumberedReplay ->
    parentCoverage := by
  intro parents
  exact parents (renumberedReplay -> parentCoverage)
    (fun replay_to_parent _parent_to_root => replay_to_parent)

theorem ay_ucir_root_empty_clause
    (renumberedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :
    AyUCIRParentCoverage renumberedReplay parentCoverage rootEmptyClause ->
    parentCoverage ->
    rootEmptyClause := by
  intro parents
  exact parents (parentCoverage -> rootEmptyClause)
    (fun _replay_to_parent parent_to_root => parent_to_root)

theorem ay_ucir_checker_transcript
    (renumberedReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUCIRCheckerTranscript renumberedReplay checkerTranscript
      transcriptAccepted ->
    renumberedReplay ->
    checkerTranscript := by
  intro transcript
  exact transcript (renumberedReplay -> checkerTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_ucir_transcript_accepted
    (renumberedReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUCIRCheckerTranscript renumberedReplay checkerTranscript
      transcriptAccepted ->
    checkerTranscript ->
    transcriptAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> transcriptAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_ucir_formula_fingerprint
    (renumberedReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUCIRFormulaFingerprint renumberedReplay formulaFingerprint
      fingerprintAccepted ->
    renumberedReplay ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (renumberedReplay -> formulaFingerprint)
    (fun replay_to_fingerprint _fingerprint_to_accept =>
      replay_to_fingerprint)

theorem ay_ucir_fingerprint_accepted
    (renumberedReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUCIRFormulaFingerprint renumberedReplay formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _replay_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_ucir_reconstruction_evidence
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCIRReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_ucir_conj_left reconstructionEvidence
    (AyUCIRConj
      (AyUCIRMap rootEmptyClause visibleUnsat)
      (AyUCIRMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_ucir_visible_unsat_from_root
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCIRReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    rootEmptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (rootEmptyClause -> visibleUnsat)
    (fun _evidence tail =>
      tail (rootEmptyClause -> visibleUnsat)
        (fun root_to_visible _visible_to_original => root_to_visible))

theorem ay_ucir_original_unsat_from_visible
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCIRReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _evidence tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _root_to_visible visible_to_original => visible_to_original))

theorem ay_ucir_accepted_evidence
    (renumberingManifest : Prop) (inverseMap : Prop)
    (renumberedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCIRAcceptedRenumbering renumberingManifest inverseMap
      renumberedReplay parentCoverage rootEmptyClause checkerTranscript
      transcriptAccepted formulaFingerprint fingerprintAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    AyUCIRAcceptedEvidence renumberingManifest inverseMap renumberedReplay
      parentCoverage rootEmptyClause checkerTranscript transcriptAccepted
      formulaFingerprint fingerprintAccepted reconstructionEvidence
      visibleUnsat originalUnsat := by
  intro accepted
  exact ay_ucir_conj_left
    (AyUCIRAcceptedEvidence renumberingManifest inverseMap
      renumberedReplay parentCoverage rootEmptyClause checkerTranscript
      transcriptAccepted formulaFingerprint fingerprintAccepted
      reconstructionEvidence visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_ucir_accepted_original_unsat
    (renumberingManifest : Prop) (inverseMap : Prop)
    (renumberedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUCIRAcceptedRenumbering renumberingManifest inverseMap
      renumberedReplay parentCoverage rootEmptyClause checkerTranscript
      transcriptAccepted formulaFingerprint fingerprintAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_ucir_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUCIRPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_ucir_disj_right noClaim originalUnsat unsat

theorem ay_ucir_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUCIRPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_ucir_disj_left noClaim originalUnsat no_claim

theorem ay_ucir_accepted_renumbering_publish_sound
    (renumberingManifest : Prop) (inverseMap : Prop)
    (renumberedReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) (noClaim : Prop) :
    AyUCIRAcceptedRenumbering renumberingManifest inverseMap
      renumberedReplay parentCoverage rootEmptyClause checkerTranscript
      transcriptAccepted formulaFingerprint fingerprintAccepted
      reconstructionEvidence visibleUnsat originalUnsat ->
    AyUCIRPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_ucir_public_unsat_report noClaim originalUnsat
    (ay_ucir_accepted_original_unsat renumberingManifest inverseMap
      renumberedReplay parentCoverage rootEmptyClause checkerTranscript
      transcriptAccepted formulaFingerprint fingerprintAccepted
      reconstructionEvidence visibleUnsat originalUnsat accepted)

theorem ay_ucir_bad_renumbering_no_claim
    (idDrift : Prop) (missingInverseMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCIRBadRenumbering idDrift missingInverseMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_ucir_conj_left noClaim recompute fail_closed)

theorem ay_ucir_bad_renumbering_recompute
    (idDrift : Prop) (missingInverseMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUCIRBadRenumbering idDrift missingInverseMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_ucir_bad_renumbering_public_no_claim
    (idDrift : Prop) (missingInverseMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUCIRBadRenumbering idDrift missingInverseMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    AyUCIRPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_ucir_public_no_claim_report noClaim originalUnsat
    (ay_ucir_bad_renumbering_no_claim idDrift missingInverseMap
      parentMismatch staleFingerprint uncheckedTranscript noClaim recompute
      bad)

theorem ay_ucir_bad_renumbering_cannot_publish
    (idDrift : Prop) (missingInverseMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUCIRBadRenumbering idDrift missingInverseMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_ucir_bad_renumbering_no_claim idDrift missingInverseMap
      parentMismatch staleFingerprint uncheckedTranscript noClaim recompute
      bad)
    unsat

theorem ay_ucir_id_drift_forces_no_claim
    (idDrift : Prop) (missingInverseMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    idDrift ->
    AyUCIRConj noClaim recompute ->
    AyUCIRBadRenumbering idDrift missingInverseMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro drift
  intro fail_closed
  exact ay_ucir_conj_intro
    (AyUCIRConj noClaim recompute)
    (AyUCIRDisj idDrift
      (AyUCIRDisj missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_ucir_disj_left idDrift
      (AyUCIRDisj missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript)))
      drift)

theorem ay_ucir_missing_inverse_map_forces_no_claim
    (idDrift : Prop) (missingInverseMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    missingInverseMap ->
    AyUCIRConj noClaim recompute ->
    AyUCIRBadRenumbering idDrift missingInverseMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro missing
  intro fail_closed
  exact ay_ucir_conj_intro
    (AyUCIRConj noClaim recompute)
    (AyUCIRDisj idDrift
      (AyUCIRDisj missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_ucir_disj_right idDrift
      (AyUCIRDisj missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript)))
      (ay_ucir_disj_left missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript))
        missing))

theorem ay_ucir_parent_mismatch_forces_no_claim
    (idDrift : Prop) (missingInverseMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    parentMismatch ->
    AyUCIRConj noClaim recompute ->
    AyUCIRBadRenumbering idDrift missingInverseMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro mismatch
  intro fail_closed
  exact ay_ucir_conj_intro
    (AyUCIRConj noClaim recompute)
    (AyUCIRDisj idDrift
      (AyUCIRDisj missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_ucir_disj_right idDrift
      (AyUCIRDisj missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript)))
      (ay_ucir_disj_right missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript))
        (ay_ucir_disj_left parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript)
          mismatch)))

theorem ay_ucir_stale_fingerprint_forces_no_claim
    (idDrift : Prop) (missingInverseMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    staleFingerprint ->
    AyUCIRConj noClaim recompute ->
    AyUCIRBadRenumbering idDrift missingInverseMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro stale
  intro fail_closed
  exact ay_ucir_conj_intro
    (AyUCIRConj noClaim recompute)
    (AyUCIRDisj idDrift
      (AyUCIRDisj missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_ucir_disj_right idDrift
      (AyUCIRDisj missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript)))
      (ay_ucir_disj_right missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript))
        (ay_ucir_disj_right parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript)
          (ay_ucir_disj_left staleFingerprint uncheckedTranscript stale))))

theorem ay_ucir_unchecked_transcript_forces_no_claim
    (idDrift : Prop) (missingInverseMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    uncheckedTranscript ->
    AyUCIRConj noClaim recompute ->
    AyUCIRBadRenumbering idDrift missingInverseMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro unchecked
  intro fail_closed
  exact ay_ucir_conj_intro
    (AyUCIRConj noClaim recompute)
    (AyUCIRDisj idDrift
      (AyUCIRDisj missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_ucir_disj_right idDrift
      (AyUCIRDisj missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript)))
      (ay_ucir_disj_right missingInverseMap
        (AyUCIRDisj parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript))
        (ay_ucir_disj_right parentMismatch
          (AyUCIRDisj staleFingerprint uncheckedTranscript)
          (ay_ucir_disj_right staleFingerprint uncheckedTranscript
            unchecked))))

theorem ay_ucir_unchecked_transcript_cannot_publish
    (idDrift : Prop) (missingInverseMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUCIRBadRenumbering idDrift missingInverseMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_ucir_bad_renumbering_cannot_publish idDrift missingInverseMap
    parentMismatch staleFingerprint uncheckedTranscript noClaim recompute
    originalUnsat bad
