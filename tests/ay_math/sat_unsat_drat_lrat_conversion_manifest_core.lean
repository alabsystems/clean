-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Bounded DRAT-to-LRAT conversion manifest soundness for ay sequential-main
-- SAT-COMP UNSAT checking. Propositions stand for converted proof artifacts,
-- conversion manifests, step maps, parent coverage, root empty clauses,
-- checker transcripts, formula fingerprints, reconstruction evidence, and
-- fail-closed no-claim/recompute diagnostics.

def AyUDLCConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUDLCDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUDLCMap (source : Prop) (target : Prop) :=
  source -> target

def AyUDLCConversionManifest
    (convertedArtifact : Prop) (conversionManifest : Prop)
    (lratReplay : Prop) :=
  AyUDLCConj convertedArtifact
    (AyUDLCConj
      (AyUDLCMap convertedArtifact conversionManifest)
      (AyUDLCMap conversionManifest lratReplay))

def AyUDLCStepMap
    (lratReplay : Prop) (stepMap : Prop)
    (stepMapAccepted : Prop) :=
  AyUDLCConj
    (AyUDLCMap lratReplay stepMap)
    (AyUDLCMap stepMap stepMapAccepted)

def AyUDLCParentCoverage
    (lratReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :=
  AyUDLCConj
    (AyUDLCMap lratReplay parentCoverage)
    (AyUDLCMap parentCoverage rootEmptyClause)

def AyUDLCCheckerTranscript
    (lratReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :=
  AyUDLCConj
    (AyUDLCMap lratReplay checkerTranscript)
    (AyUDLCMap checkerTranscript transcriptAccepted)

def AyUDLCFormulaFingerprint
    (lratReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :=
  AyUDLCConj
    (AyUDLCMap lratReplay formulaFingerprint)
    (AyUDLCMap formulaFingerprint fingerprintAccepted)

def AyUDLCReconstruction
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUDLCConj reconstructionEvidence
    (AyUDLCConj
      (AyUDLCMap rootEmptyClause visibleUnsat)
      (AyUDLCMap visibleUnsat originalUnsat))

def AyUDLCAcceptedEvidence
    (convertedArtifact : Prop) (conversionManifest : Prop)
    (lratReplay : Prop) (stepMap : Prop) (stepMapAccepted : Prop)
    (parentCoverage : Prop) (rootEmptyClause : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (reconstructionEvidence : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUDLCConj
    (AyUDLCConversionManifest convertedArtifact conversionManifest
      lratReplay)
    (AyUDLCConj
      (AyUDLCStepMap lratReplay stepMap stepMapAccepted)
      (AyUDLCConj
        (AyUDLCParentCoverage lratReplay parentCoverage rootEmptyClause)
        (AyUDLCConj
          (AyUDLCCheckerTranscript lratReplay checkerTranscript
            transcriptAccepted)
          (AyUDLCConj
            (AyUDLCFormulaFingerprint lratReplay formulaFingerprint
              fingerprintAccepted)
            (AyUDLCReconstruction rootEmptyClause reconstructionEvidence
              visibleUnsat originalUnsat)))))

def AyUDLCAcceptedConversion
    (convertedArtifact : Prop) (conversionManifest : Prop)
    (lratReplay : Prop) (stepMap : Prop) (stepMapAccepted : Prop)
    (parentCoverage : Prop) (rootEmptyClause : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (reconstructionEvidence : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :=
  AyUDLCConj
    (AyUDLCAcceptedEvidence convertedArtifact conversionManifest
      lratReplay stepMap stepMapAccepted parentCoverage rootEmptyClause
      checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat)
    originalUnsat

def AyUDLCBadConversion
    (conversionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :=
  AyUDLCConj
    (AyUDLCConj noClaim recompute)
    (AyUDLCDisj conversionDrift
      (AyUDLCDisj missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript))))

def AyUDLCPublicReport (noClaim : Prop) (originalUnsat : Prop) :=
  AyUDLCDisj noClaim originalUnsat

theorem ay_udlc_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUDLCConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_udlc_conj_left
    (p : Prop) (q : Prop) :
    AyUDLCConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_udlc_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUDLCDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_udlc_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUDLCDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_udlc_converted_artifact
    (convertedArtifact : Prop) (conversionManifest : Prop)
    (lratReplay : Prop) :
    AyUDLCConversionManifest convertedArtifact conversionManifest
      lratReplay ->
    convertedArtifact := by
  intro manifest
  exact manifest convertedArtifact
    (fun artifact _tail => artifact)

theorem ay_udlc_conversion_manifest
    (convertedArtifact : Prop) (conversionManifest : Prop)
    (lratReplay : Prop) :
    AyUDLCConversionManifest convertedArtifact conversionManifest
      lratReplay ->
    conversionManifest := by
  intro manifest
  exact manifest conversionManifest
    (fun (artifact : convertedArtifact) tail =>
      tail conversionManifest
        (fun artifact_to_manifest _manifest_to_replay =>
          artifact_to_manifest artifact))

theorem ay_udlc_lrat_replay
    (convertedArtifact : Prop) (conversionManifest : Prop)
    (lratReplay : Prop) :
    AyUDLCConversionManifest convertedArtifact conversionManifest
      lratReplay ->
    lratReplay := by
  intro manifest
  exact manifest lratReplay
    (fun (artifact : convertedArtifact) tail =>
      tail lratReplay
        (fun artifact_to_manifest manifest_to_replay =>
          manifest_to_replay (artifact_to_manifest artifact)))

theorem ay_udlc_step_map
    (lratReplay : Prop) (stepMap : Prop) (stepMapAccepted : Prop) :
    AyUDLCStepMap lratReplay stepMap stepMapAccepted ->
    lratReplay ->
    stepMap := by
  intro step
  exact step (lratReplay -> stepMap)
    (fun replay_to_step _step_to_accept => replay_to_step)

theorem ay_udlc_step_map_accepted
    (lratReplay : Prop) (stepMap : Prop) (stepMapAccepted : Prop) :
    AyUDLCStepMap lratReplay stepMap stepMapAccepted ->
    stepMap ->
    stepMapAccepted := by
  intro step
  exact step (stepMap -> stepMapAccepted)
    (fun _replay_to_step step_to_accept => step_to_accept)

theorem ay_udlc_parent_coverage
    (lratReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :
    AyUDLCParentCoverage lratReplay parentCoverage rootEmptyClause ->
    lratReplay ->
    parentCoverage := by
  intro parents
  exact parents (lratReplay -> parentCoverage)
    (fun replay_to_parent _parent_to_root => replay_to_parent)

theorem ay_udlc_root_empty_clause
    (lratReplay : Prop) (parentCoverage : Prop)
    (rootEmptyClause : Prop) :
    AyUDLCParentCoverage lratReplay parentCoverage rootEmptyClause ->
    parentCoverage ->
    rootEmptyClause := by
  intro parents
  exact parents (parentCoverage -> rootEmptyClause)
    (fun _replay_to_parent parent_to_root => parent_to_root)

theorem ay_udlc_checker_transcript
    (lratReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUDLCCheckerTranscript lratReplay checkerTranscript
      transcriptAccepted ->
    lratReplay ->
    checkerTranscript := by
  intro transcript
  exact transcript (lratReplay -> checkerTranscript)
    (fun replay_to_transcript _transcript_to_accept =>
      replay_to_transcript)

theorem ay_udlc_transcript_accepted
    (lratReplay : Prop) (checkerTranscript : Prop)
    (transcriptAccepted : Prop) :
    AyUDLCCheckerTranscript lratReplay checkerTranscript
      transcriptAccepted ->
    checkerTranscript ->
    transcriptAccepted := by
  intro transcript
  exact transcript (checkerTranscript -> transcriptAccepted)
    (fun _replay_to_transcript transcript_to_accept =>
      transcript_to_accept)

theorem ay_udlc_formula_fingerprint
    (lratReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUDLCFormulaFingerprint lratReplay formulaFingerprint
      fingerprintAccepted ->
    lratReplay ->
    formulaFingerprint := by
  intro fingerprint
  exact fingerprint (lratReplay -> formulaFingerprint)
    (fun replay_to_fingerprint _fingerprint_to_accept =>
      replay_to_fingerprint)

theorem ay_udlc_fingerprint_accepted
    (lratReplay : Prop) (formulaFingerprint : Prop)
    (fingerprintAccepted : Prop) :
    AyUDLCFormulaFingerprint lratReplay formulaFingerprint
      fingerprintAccepted ->
    formulaFingerprint ->
    fingerprintAccepted := by
  intro fingerprint
  exact fingerprint (formulaFingerprint -> fingerprintAccepted)
    (fun _replay_to_fingerprint fingerprint_to_accept =>
      fingerprint_to_accept)

theorem ay_udlc_reconstruction_evidence
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDLCReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    reconstructionEvidence := by
  intro reconstruction
  exact ay_udlc_conj_left reconstructionEvidence
    (AyUDLCConj
      (AyUDLCMap rootEmptyClause visibleUnsat)
      (AyUDLCMap visibleUnsat originalUnsat))
    reconstruction

theorem ay_udlc_visible_unsat_from_root
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDLCReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    rootEmptyClause ->
    visibleUnsat := by
  intro reconstruction
  exact reconstruction (rootEmptyClause -> visibleUnsat)
    (fun _evidence tail =>
      tail (rootEmptyClause -> visibleUnsat)
        (fun root_to_visible _visible_to_original => root_to_visible))

theorem ay_udlc_original_unsat_from_visible
    (rootEmptyClause : Prop) (reconstructionEvidence : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUDLCReconstruction rootEmptyClause reconstructionEvidence
      visibleUnsat originalUnsat ->
    visibleUnsat ->
    originalUnsat := by
  intro reconstruction
  exact reconstruction (visibleUnsat -> originalUnsat)
    (fun _evidence tail =>
      tail (visibleUnsat -> originalUnsat)
        (fun _root_to_visible visible_to_original => visible_to_original))

theorem ay_udlc_accepted_evidence
    (convertedArtifact : Prop) (conversionManifest : Prop)
    (lratReplay : Prop) (stepMap : Prop) (stepMapAccepted : Prop)
    (parentCoverage : Prop) (rootEmptyClause : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (reconstructionEvidence : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDLCAcceptedConversion convertedArtifact conversionManifest
      lratReplay stepMap stepMapAccepted parentCoverage rootEmptyClause
      checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat ->
    AyUDLCAcceptedEvidence convertedArtifact conversionManifest
      lratReplay stepMap stepMapAccepted parentCoverage rootEmptyClause
      checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat := by
  intro accepted
  exact ay_udlc_conj_left
    (AyUDLCAcceptedEvidence convertedArtifact conversionManifest
      lratReplay stepMap stepMapAccepted parentCoverage rootEmptyClause
      checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat)
    originalUnsat
    accepted

theorem ay_udlc_accepted_original_unsat
    (convertedArtifact : Prop) (conversionManifest : Prop)
    (lratReplay : Prop) (stepMap : Prop) (stepMapAccepted : Prop)
    (parentCoverage : Prop) (rootEmptyClause : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (reconstructionEvidence : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) :
    AyUDLCAcceptedConversion convertedArtifact conversionManifest
      lratReplay stepMap stepMapAccepted parentCoverage rootEmptyClause
      checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat ->
    originalUnsat := by
  intro accepted
  exact accepted originalUnsat (fun _evidence unsat => unsat)

theorem ay_udlc_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) :
    originalUnsat -> AyUDLCPublicReport noClaim originalUnsat := by
  intro unsat
  exact ay_udlc_disj_right noClaim originalUnsat unsat

theorem ay_udlc_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) :
    noClaim -> AyUDLCPublicReport noClaim originalUnsat := by
  intro no_claim
  exact ay_udlc_disj_left noClaim originalUnsat no_claim

theorem ay_udlc_accepted_conversion_publish_sound
    (convertedArtifact : Prop) (conversionManifest : Prop)
    (lratReplay : Prop) (stepMap : Prop) (stepMapAccepted : Prop)
    (parentCoverage : Prop) (rootEmptyClause : Prop)
    (checkerTranscript : Prop) (transcriptAccepted : Prop)
    (formulaFingerprint : Prop) (fingerprintAccepted : Prop)
    (reconstructionEvidence : Prop) (visibleUnsat : Prop)
    (originalUnsat : Prop) (noClaim : Prop) :
    AyUDLCAcceptedConversion convertedArtifact conversionManifest
      lratReplay stepMap stepMapAccepted parentCoverage rootEmptyClause
      checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat ->
    AyUDLCPublicReport noClaim originalUnsat := by
  intro accepted
  exact ay_udlc_public_unsat_report noClaim originalUnsat
    (ay_udlc_accepted_original_unsat convertedArtifact conversionManifest
      lratReplay stepMap stepMapAccepted parentCoverage rootEmptyClause
      checkerTranscript transcriptAccepted formulaFingerprint
      fingerprintAccepted reconstructionEvidence visibleUnsat originalUnsat
      accepted)

theorem ay_udlc_bad_conversion_no_claim
    (conversionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUDLCBadConversion conversionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun fail_closed _reason =>
      ay_udlc_conj_left noClaim recompute fail_closed)

theorem ay_udlc_bad_conversion_recompute
    (conversionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    AyUDLCBadConversion conversionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun fail_closed _reason =>
      fail_closed recompute (fun _no_claim recompute_proof => recompute_proof))

theorem ay_udlc_bad_conversion_public_no_claim
    (conversionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUDLCBadConversion conversionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    AyUDLCPublicReport noClaim originalUnsat := by
  intro bad
  exact ay_udlc_public_no_claim_report noClaim originalUnsat
    (ay_udlc_bad_conversion_no_claim conversionDrift missingStepMap
      parentMismatch staleFingerprint uncheckedTranscript noClaim recompute
      bad)

theorem ay_udlc_bad_conversion_cannot_publish
    (conversionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUDLCBadConversion conversionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_udlc_bad_conversion_no_claim conversionDrift missingStepMap
      parentMismatch staleFingerprint uncheckedTranscript noClaim recompute
      bad)
    unsat

theorem ay_udlc_conversion_drift_forces_no_claim
    (conversionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    conversionDrift ->
    AyUDLCConj noClaim recompute ->
    AyUDLCBadConversion conversionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro drift
  intro fail_closed
  exact ay_udlc_conj_intro
    (AyUDLCConj noClaim recompute)
    (AyUDLCDisj conversionDrift
      (AyUDLCDisj missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_udlc_disj_left conversionDrift
      (AyUDLCDisj missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript)))
      drift)

theorem ay_udlc_missing_step_map_forces_no_claim
    (conversionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    missingStepMap ->
    AyUDLCConj noClaim recompute ->
    AyUDLCBadConversion conversionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro missing
  intro fail_closed
  exact ay_udlc_conj_intro
    (AyUDLCConj noClaim recompute)
    (AyUDLCDisj conversionDrift
      (AyUDLCDisj missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_udlc_disj_right conversionDrift
      (AyUDLCDisj missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript)))
      (ay_udlc_disj_left missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript))
        missing))

theorem ay_udlc_parent_mismatch_forces_no_claim
    (conversionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    parentMismatch ->
    AyUDLCConj noClaim recompute ->
    AyUDLCBadConversion conversionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro mismatch
  intro fail_closed
  exact ay_udlc_conj_intro
    (AyUDLCConj noClaim recompute)
    (AyUDLCDisj conversionDrift
      (AyUDLCDisj missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_udlc_disj_right conversionDrift
      (AyUDLCDisj missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript)))
      (ay_udlc_disj_right missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript))
        (ay_udlc_disj_left parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript)
          mismatch)))

theorem ay_udlc_stale_fingerprint_forces_no_claim
    (conversionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    staleFingerprint ->
    AyUDLCConj noClaim recompute ->
    AyUDLCBadConversion conversionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro stale
  intro fail_closed
  exact ay_udlc_conj_intro
    (AyUDLCConj noClaim recompute)
    (AyUDLCDisj conversionDrift
      (AyUDLCDisj missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_udlc_disj_right conversionDrift
      (AyUDLCDisj missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript)))
      (ay_udlc_disj_right missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript))
        (ay_udlc_disj_right parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript)
          (ay_udlc_disj_left staleFingerprint uncheckedTranscript stale))))

theorem ay_udlc_unchecked_transcript_forces_no_claim
    (conversionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop) :
    uncheckedTranscript ->
    AyUDLCConj noClaim recompute ->
    AyUDLCBadConversion conversionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute := by
  intro unchecked
  intro fail_closed
  exact ay_udlc_conj_intro
    (AyUDLCConj noClaim recompute)
    (AyUDLCDisj conversionDrift
      (AyUDLCDisj missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript))))
    fail_closed
    (ay_udlc_disj_right conversionDrift
      (AyUDLCDisj missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript)))
      (ay_udlc_disj_right missingStepMap
        (AyUDLCDisj parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript))
        (ay_udlc_disj_right parentMismatch
          (AyUDLCDisj staleFingerprint uncheckedTranscript)
          (ay_udlc_disj_right staleFingerprint uncheckedTranscript
            unchecked))))

theorem ay_udlc_unchecked_transcript_cannot_publish
    (conversionDrift : Prop) (missingStepMap : Prop)
    (parentMismatch : Prop) (staleFingerprint : Prop)
    (uncheckedTranscript : Prop) (noClaim : Prop) (recompute : Prop)
    (originalUnsat : Prop) :
    AyUDLCBadConversion conversionDrift missingStepMap parentMismatch
      staleFingerprint uncheckedTranscript noClaim recompute ->
    (noClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro bad
  exact ay_udlc_bad_conversion_cannot_publish conversionDrift missingStepMap
    parentMismatch staleFingerprint uncheckedTranscript noClaim recompute
    originalUnsat bad
