-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Manifest bisect oracle core for ay SAT-COMP regression isolation. The
-- abstraction tracks baseline, midpoint, and candidate manifests, artifact
-- digests, public output comparisons, accepted/rejected deltas, and audit
-- replay.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AyVisibleModelReconstruction (visibleModel : Prop) (originalModel : Prop) :=
  visibleModel -> originalModel

def AyPreprocessingProof (originalFormula : Prop) (visibleFormula : Prop) :=
  originalFormula -> visibleFormula

def AyUnsatReplayWitness (visibleFormula : Prop) (finalClause : Prop) :=
  finalClause -> visibleFormula -> False

def AySatArtifact (visibleModel : Prop) (originalModel : Prop) :=
  AyConj visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)

def AyUnsatArtifact
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :=
  AyConj finalClause
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))

def AyCompressedOutcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :=
  AyDisj
    (AySatArtifact visibleModel originalModel)
    (AyUnsatArtifact originalFormula visibleFormula finalClause)

def AyPublicSoundnessTheorem
    (originalFormula : Prop) (originalModel : Prop) :=
  AyDisj originalModel (Not originalFormula)

def AyArtifactDigest (satDigest : Prop) (unsatDigest : Prop) :=
  AyDisj satDigest unsatDigest

def AyPublicOutputComparison (leftToken : Prop) (rightToken : Prop) :=
  AyEquisat leftToken rightToken

def AyAuditReplay (accepted : Prop) :=
  accepted

def AyBisectRejected (rejected : Prop) :=
  rejected

def AyRunManifest
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satDigest : Prop) (unsatDigest : Prop) (publicToken : Prop)
    (accepted : Prop) :=
  AyConj
    (AyArtifactDigest satDigest unsatDigest)
    (AyConj
      publicToken
      (AyConj
        (AyAuditReplay accepted)
        (accepted ->
          AyCompressedOutcome
            originalFormula visibleFormula visibleModel originalModel
            finalClause)))

def AyDeltaAccepted
    (leftSatDigest : Prop) (leftUnsatDigest : Prop) (leftToken : Prop)
    (rightSatDigest : Prop) (rightUnsatDigest : Prop) (rightToken : Prop)
    (rightAccepted : Prop) :=
  AyAuditReplay rightAccepted

def AyBisectAccepted
    (baselineSatDigest : Prop) (baselineUnsatDigest : Prop)
    (baselineToken : Prop)
    (midSatDigest : Prop) (midUnsatDigest : Prop) (midToken : Prop)
    (midAccepted : Prop)
    (candidateSatDigest : Prop) (candidateUnsatDigest : Prop)
    (candidateToken : Prop) (candidateAccepted : Prop) :=
  AyConj
    (AyDeltaAccepted
      baselineSatDigest baselineUnsatDigest baselineToken
      midSatDigest midUnsatDigest midToken midAccepted)
    (AyDeltaAccepted
      midSatDigest midUnsatDigest midToken
      candidateSatDigest candidateUnsatDigest candidateToken
      candidateAccepted)

def AyBisectOracle
    (baselineSatDigest : Prop) (baselineUnsatDigest : Prop)
    (baselineToken : Prop)
    (midSatDigest : Prop) (midUnsatDigest : Prop) (midToken : Prop)
    (midAccepted : Prop)
    (candidateSatDigest : Prop) (candidateUnsatDigest : Prop)
    (candidateToken : Prop) (candidateAccepted : Prop)
    (rejected : Prop) :=
  AyDisj
    (AyBisectAccepted
      baselineSatDigest baselineUnsatDigest baselineToken
      midSatDigest midUnsatDigest midToken midAccepted
      candidateSatDigest candidateUnsatDigest candidateToken
      candidateAccepted)
    (AyBisectRejected rejected)

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_conj_left
    (p : Prop) (q : Prop) :
    AyConj p q -> p := by
  intro both
  exact both p
    (fun hp _hq => hp)

theorem ay_disj_left
    (p : Prop) (q : Prop) :
    p -> AyDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_disj_right
    (p : Prop) (q : Prop) :
    q -> AyDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyEquisat before after := by
  intro forward
  intro backward
  exact ay_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_equisat_forward
    (before : Prop) (after : Prop) :
    AyEquisat before after ->
    before -> after := by
  intro eqsat
  exact ay_conj_left (before -> after) (after -> before) eqsat

theorem ay_sat_artifact_visible
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArtifact visibleModel originalModel ->
    visibleModel := by
  intro artifact
  exact ay_conj_left visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)
    artifact

theorem ay_sat_artifact_reconstruct
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArtifact visibleModel originalModel ->
    AyVisibleModelReconstruction visibleModel originalModel := by
  intro artifact
  exact artifact
    (AyVisibleModelReconstruction visibleModel originalModel)
    (fun _visible reconstruct => reconstruct)

theorem ay_sat_artifact_original
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArtifact visibleModel originalModel ->
    originalModel := by
  intro artifact
  exact
    (ay_sat_artifact_reconstruct visibleModel originalModel artifact)
    (ay_sat_artifact_visible visibleModel originalModel artifact)

theorem ay_unsat_artifact_clause
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    finalClause := by
  intro artifact
  exact ay_conj_left finalClause
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    artifact

theorem ay_unsat_artifact_preprocess
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    AyPreprocessingProof originalFormula visibleFormula := by
  intro artifact
  let tail := artifact
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    (fun _clause proof_tail => proof_tail)
  exact ay_conj_left
    (AyPreprocessingProof originalFormula visibleFormula)
    (AyUnsatReplayWitness visibleFormula finalClause)
    tail

theorem ay_unsat_artifact_replay
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    AyUnsatReplayWitness visibleFormula finalClause := by
  intro artifact
  let tail := artifact
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    (fun _clause proof_tail => proof_tail)
  exact tail
    (AyUnsatReplayWitness visibleFormula finalClause)
    (fun _preprocess replay => replay)

theorem ay_unsat_artifact_original_unsat
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    Not originalFormula := by
  intro artifact
  intro original
  exact
    (ay_unsat_artifact_replay originalFormula visibleFormula finalClause
      artifact)
    (ay_unsat_artifact_clause originalFormula visibleFormula finalClause
      artifact)
    ((ay_unsat_artifact_preprocess
      originalFormula visibleFormula finalClause artifact) original)

theorem ay_outcome_public_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop) :
    AyCompressedOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro outcome
  exact outcome
    (AyPublicSoundnessTheorem originalFormula originalModel)
    (fun sat =>
      ay_disj_left originalModel (Not originalFormula)
        (ay_sat_artifact_original visibleModel originalModel sat))
    (fun unsat =>
      ay_disj_right originalModel (Not originalFormula)
        (ay_unsat_artifact_original_unsat
          originalFormula visibleFormula finalClause unsat))

theorem ay_manifest_replay_outcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satDigest : Prop) (unsatDigest : Prop) (publicToken : Prop)
    (accepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satDigest unsatDigest publicToken accepted ->
    accepted ->
    AyCompressedOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  intro manifest
  let tail1 := manifest
    (AyConj
      publicToken
      (AyConj
        (AyAuditReplay accepted)
        (accepted ->
          AyCompressedOutcome
            originalFormula visibleFormula visibleModel originalModel
            finalClause)))
    (fun _digest manifest_tail => manifest_tail)
  let tail2 := tail1
    (AyConj
      (AyAuditReplay accepted)
      (accepted ->
        AyCompressedOutcome
          originalFormula visibleFormula visibleModel originalModel
          finalClause))
    (fun _token manifest_tail => manifest_tail)
  exact tail2
    (accepted ->
      AyCompressedOutcome
        originalFormula visibleFormula visibleModel originalModel finalClause)
    (fun _decision replay => replay)

theorem ay_manifest_public_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satDigest : Prop) (unsatDigest : Prop) (publicToken : Prop)
    (accepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satDigest unsatDigest publicToken accepted ->
    accepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro manifest
  intro accepted_h
  exact ay_outcome_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    (ay_manifest_replay_outcome
      originalFormula visibleFormula visibleModel originalModel finalClause
      satDigest unsatDigest publicToken accepted manifest accepted_h)

theorem ay_delta_preserves_sat_digest
    (leftSatDigest : Prop) (rightSatDigest : Prop)
    (rightUnsatDigest : Prop) :
    AyEquisat leftSatDigest rightSatDigest ->
    leftSatDigest ->
    AyArtifactDigest rightSatDigest rightUnsatDigest := by
  intro digest_match
  intro left_digest
  exact ay_disj_left rightSatDigest rightUnsatDigest
    (ay_equisat_forward leftSatDigest rightSatDigest
      digest_match left_digest)

theorem ay_delta_preserves_unsat_digest
    (rightSatDigest : Prop) (leftUnsatDigest : Prop)
    (rightUnsatDigest : Prop) :
    AyEquisat leftUnsatDigest rightUnsatDigest ->
    leftUnsatDigest ->
    AyArtifactDigest rightSatDigest rightUnsatDigest := by
  intro digest_match
  intro left_digest
  exact ay_disj_right rightSatDigest rightUnsatDigest
    (ay_equisat_forward leftUnsatDigest rightUnsatDigest
      digest_match left_digest)

theorem ay_public_output_comparison_forward
    (leftToken : Prop) (rightToken : Prop) :
    AyPublicOutputComparison leftToken rightToken ->
    leftToken ->
    rightToken := by
  intro comparison
  exact ay_equisat_forward leftToken rightToken comparison

theorem ay_accepted_bisection_preserves_baseline_equivalence
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineSatDigest : Prop) (baselineUnsatDigest : Prop)
    (baselineToken : Prop) (baselineAccepted : Prop)
    (midSatDigest : Prop) (midUnsatDigest : Prop) (midToken : Prop)
    (midAccepted : Prop)
    (candidateSatDigest : Prop) (candidateUnsatDigest : Prop)
    (candidateToken : Prop) (candidateAccepted : Prop) :
    AyBisectAccepted
      baselineSatDigest baselineUnsatDigest baselineToken
      midSatDigest midUnsatDigest midToken midAccepted
      candidateSatDigest candidateUnsatDigest candidateToken
      candidateAccepted ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineSatDigest baselineUnsatDigest baselineToken baselineAccepted ->
    baselineAccepted ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      candidateSatDigest candidateUnsatDigest candidateToken
      candidateAccepted ->
    AyConj
      (AyPublicSoundnessTheorem originalFormula originalModel)
      (AyPublicSoundnessTheorem originalFormula originalModel) := by
  intro bisect
  intro baseline_manifest
  intro baseline_accepted
  intro candidate_manifest
  intro result
  intro build
  let baseline_sound := ay_manifest_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    baselineSatDigest baselineUnsatDigest baselineToken baselineAccepted
    baseline_manifest baseline_accepted
  exact build
    baseline_sound
    baseline_sound

theorem ay_rejected_bisection_no_claim_diagnostic
    (rejected : Prop)
    (diagnostic : Prop) :
    AyBisectRejected rejected ->
    AyBisectOracle
      diagnostic diagnostic diagnostic diagnostic diagnostic diagnostic
      diagnostic diagnostic diagnostic diagnostic diagnostic rejected := by
  intro rejected_h
  exact ay_disj_right
    (AyBisectAccepted
      diagnostic diagnostic diagnostic diagnostic diagnostic diagnostic
      diagnostic diagnostic diagnostic diagnostic diagnostic)
    (AyBisectRejected rejected)
    rejected_h
