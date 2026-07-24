-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Optimization-gate theorem for ay SAT-COMP experiments. The gate either
-- accepts an optimized path with checker/artifact evidence, or falls back to
-- baseline soundness while exposing only localized bisection diagnostics.

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

def AyAuditReplay (accepted : Prop) : Prop :=
  AyConj accepted accepted

def AyArtifactEquality (baselineArtifact : Prop) (optimizedArtifact : Prop) :=
  AyEquisat baselineArtifact optimizedArtifact

def AyCheckerEvidence (checked : Prop) : Prop :=
  AyConj checked checked

def AyLocalizedBisectMismatch
    (prefixAgree : Prop) (firstMismatch : Prop) (diagnostic : Prop) :=
  AyConj prefixAgree (AyConj firstMismatch diagnostic)

def AyRejectedDiagnostic
    (prefixAgree : Prop) (firstMismatch : Prop) (diagnostic : Prop)
    (rejected : Prop) :=
  AyConj
    rejected
    (AyLocalizedBisectMismatch prefixAgree firstMismatch diagnostic)

def AyRunManifest
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (accepted : Prop) : Prop :=
  AyConj
    (AyAuditReplay accepted)
    (accepted ->
      AyCompressedOutcome
        originalFormula visibleFormula visibleModel originalModel finalClause)

def AyOptimizationGateAccepted
    (baselineArtifact : Prop) (optimizedArtifact : Prop)
    (checkerAccepted : Prop) (optimizedAccepted : Prop) :=
  AyConj
    (AyArtifactEquality baselineArtifact optimizedArtifact)
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyAuditReplay optimizedAccepted))

def AyOptimizationGateRejected
    (prefixAgree : Prop) (firstMismatch : Prop) (diagnostic : Prop)
    (rejected : Prop) :=
  AyRejectedDiagnostic prefixAgree firstMismatch diagnostic rejected

def AyOptimizationGate
    (baselineArtifact : Prop) (optimizedArtifact : Prop)
    (checkerAccepted : Prop) (optimizedAccepted : Prop)
    (prefixAgree : Prop) (firstMismatch : Prop) (diagnostic : Prop)
    (rejected : Prop) :=
  AyDisj
    (AyOptimizationGateAccepted
      baselineArtifact optimizedArtifact checkerAccepted optimizedAccepted)
    (AyOptimizationGateRejected
      prefixAgree firstMismatch diagnostic rejected)

theorem ay_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyConj p q := by
  intro hp
  intro hq
  intro result
  intro build_pair
  exact build_pair hp hq

theorem ay_conj_left
    (p : Prop) (q : Prop) :
    AyConj p q -> p := by
  intro both
  exact both p
    (fun (hp : p) (_hq : q) => hp)

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

theorem ay_manifest_public_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (accepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      accepted ->
    accepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro manifest
  intro accepted_h
  let replay := manifest
    (accepted ->
      AyCompressedOutcome
        originalFormula visibleFormula visibleModel originalModel finalClause)
    (fun _accepted replay => replay)
  exact ay_outcome_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    (replay accepted_h)

theorem ay_gate_acceptance_checker
    (baselineArtifact : Prop) (optimizedArtifact : Prop)
    (checkerAccepted : Prop) (optimizedAccepted : Prop) :
    AyOptimizationGateAccepted
      baselineArtifact optimizedArtifact checkerAccepted optimizedAccepted ->
    checkerAccepted := by
  intro gate
  let tail := gate
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyAuditReplay optimizedAccepted))
    (fun _artifact_eq gate_tail => gate_tail)
  let checked_pair := ay_conj_left
    (AyCheckerEvidence checkerAccepted)
    (AyAuditReplay optimizedAccepted)
    tail
  exact ay_conj_left checkerAccepted checkerAccepted checked_pair

theorem ay_gate_acceptance_replay
    (baselineArtifact : Prop) (optimizedArtifact : Prop)
    (checkerAccepted : Prop) (optimizedAccepted : Prop) :
    AyOptimizationGateAccepted
      baselineArtifact optimizedArtifact checkerAccepted optimizedAccepted ->
    optimizedAccepted := by
  intro gate
  let tail := gate
    (AyConj
      (AyCheckerEvidence checkerAccepted)
      (AyAuditReplay optimizedAccepted))
    (fun _artifact_eq gate_tail => gate_tail)
  let replay_pair := tail
    (AyAuditReplay optimizedAccepted)
    (fun _checker replay => replay)
  exact ay_conj_left optimizedAccepted optimizedAccepted replay_pair

theorem ay_gate_accepted_optimized_public_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineArtifact : Prop) (optimizedArtifact : Prop)
    (checkerAccepted : Prop) (optimizedAccepted : Prop) :
    AyOptimizationGateAccepted
      baselineArtifact optimizedArtifact checkerAccepted optimizedAccepted ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      optimizedAccepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro gate
  intro optimized_manifest
  exact ay_manifest_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    optimizedAccepted
    optimized_manifest
    (ay_gate_acceptance_replay
      baselineArtifact optimizedArtifact checkerAccepted optimizedAccepted gate)

theorem ay_fallback_preserves_baseline_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineAccepted : Prop)
    (prefixAgree : Prop) (firstMismatch : Prop) (diagnostic : Prop)
    (rejected : Prop) :
    AyOptimizationGateRejected
      prefixAgree firstMismatch diagnostic rejected ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineAccepted ->
    baselineAccepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro _rejected_gate
  intro baseline_manifest
  intro baseline_accepted
  exact ay_manifest_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    baselineAccepted
    baseline_manifest
    baseline_accepted

theorem ay_no_claim_rejection_diagnostic
    (prefixAgree : Prop) (firstMismatch : Prop) (diagnostic : Prop)
    (rejected : Prop) :
    AyOptimizationGateRejected
      prefixAgree firstMismatch diagnostic rejected ->
    AyConj
      (AyLocalizedBisectMismatch prefixAgree firstMismatch diagnostic)
      (AyOptimizationGateRejected
        prefixAgree firstMismatch diagnostic rejected) := by
  intro rejected_gate
  exact ay_conj_intro
    (AyLocalizedBisectMismatch prefixAgree firstMismatch diagnostic)
    (AyOptimizationGateRejected
      prefixAgree firstMismatch diagnostic rejected)
    (rejected_gate
      (AyLocalizedBisectMismatch prefixAgree firstMismatch diagnostic)
      (fun _rejected mismatch => mismatch))
    rejected_gate

theorem ay_rejection_cannot_create_optimized_soundness
    (prefixAgree : Prop) (firstMismatch : Prop) (diagnostic : Prop)
    (rejected : Prop) (semanticClaim : Prop) :
    AyOptimizationGateRejected
      prefixAgree firstMismatch diagnostic rejected ->
    semanticClaim ->
    semanticClaim := by
  intro _rejected_gate
  intro claim
  exact claim

theorem ay_safe_optimization_deployment_accept
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineArtifact : Prop) (optimizedArtifact : Prop)
    (checkerAccepted : Prop) (optimizedAccepted : Prop)
    (prefixAgree : Prop) (firstMismatch : Prop) (diagnostic : Prop)
    (rejected : Prop) :
    AyOptimizationGate
      baselineArtifact optimizedArtifact checkerAccepted optimizedAccepted
      prefixAgree firstMismatch diagnostic rejected ->
    AyOptimizationGateAccepted
      baselineArtifact optimizedArtifact checkerAccepted optimizedAccepted ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      optimizedAccepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro _gate
  intro accepted_gate
  intro optimized_manifest
  exact ay_gate_accepted_optimized_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    baselineArtifact optimizedArtifact checkerAccepted optimizedAccepted
    accepted_gate optimized_manifest

theorem ay_safe_optimization_deployment_fallback
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineAccepted : Prop)
    (prefixAgree : Prop) (firstMismatch : Prop) (diagnostic : Prop)
    (rejected : Prop) :
    AyOptimizationGateRejected
      prefixAgree firstMismatch diagnostic rejected ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineAccepted ->
    baselineAccepted ->
    AyConj
      (AyPublicSoundnessTheorem originalFormula originalModel)
      (AyLocalizedBisectMismatch prefixAgree firstMismatch diagnostic) := by
  intro rejected_gate
  intro baseline_manifest
  intro baseline_accepted
  exact ay_conj_intro
    (AyPublicSoundnessTheorem originalFormula originalModel)
    (AyLocalizedBisectMismatch prefixAgree firstMismatch diagnostic)
    (ay_fallback_preserves_baseline_soundness
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineAccepted prefixAgree firstMismatch diagnostic rejected
      rejected_gate baseline_manifest baseline_accepted)
    (rejected_gate
      (AyLocalizedBisectMismatch prefixAgree firstMismatch diagnostic)
      (fun _rejected mismatch => mismatch))

