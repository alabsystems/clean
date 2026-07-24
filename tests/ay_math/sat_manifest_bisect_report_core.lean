-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Reports emitted by the ay SAT-COMP manifest bisect oracle. Accepted reports
-- carry replay evidence plus baseline/candidate comparison diagnostics.
-- Rejected reports carry diagnostics only and deliberately expose no semantic
-- SAT/UNSAT theorem.

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

def AyArtifactDigestDiagnostic
    (satDigest : Prop) (unsatDigest : Prop) :=
  AyDisj satDigest unsatDigest

def AyPublicOutputComparison (baselineToken : Prop) (candidateToken : Prop) :=
  AyEquisat baselineToken candidateToken

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
    (AyArtifactDigestDiagnostic satDigest unsatDigest)
    (AyConj
      publicToken
      (AyConj
        (AyAuditReplay accepted)
        (accepted ->
          AyCompressedOutcome
            originalFormula visibleFormula visibleModel originalModel
            finalClause)))

def AyAcceptedBisectReport
    (baselineSatDigest : Prop) (baselineUnsatDigest : Prop)
    (baselineToken : Prop) (baselineAccepted : Prop)
    (candidateSatDigest : Prop) (candidateUnsatDigest : Prop)
    (candidateToken : Prop) :=
  AyConj
    (AyAuditReplay baselineAccepted)
    (AyConj
      (AyPublicOutputComparison baselineToken candidateToken)
      (AyConj
        (AyArtifactDigestDiagnostic baselineSatDigest baselineUnsatDigest)
        (AyArtifactDigestDiagnostic candidateSatDigest candidateUnsatDigest)))

def AyRejectedBisectReport
    (baselineSatDigest : Prop) (baselineUnsatDigest : Prop)
    (candidateSatDigest : Prop) (candidateUnsatDigest : Prop)
    (baselineToken : Prop) (candidateToken : Prop) (rejected : Prop) :=
  AyConj
    (AyBisectRejected rejected)
    (AyConj
      (AyArtifactDigestDiagnostic baselineSatDigest baselineUnsatDigest)
      (AyConj
        (AyArtifactDigestDiagnostic candidateSatDigest candidateUnsatDigest)
        (AyPublicOutputComparison baselineToken candidateToken)))

def AyBisectReport
    (baselineSatDigest : Prop) (baselineUnsatDigest : Prop)
    (baselineToken : Prop) (baselineAccepted : Prop)
    (candidateSatDigest : Prop) (candidateUnsatDigest : Prop)
    (candidateToken : Prop) (rejected : Prop) :=
  AyDisj
    (AyAcceptedBisectReport
      baselineSatDigest baselineUnsatDigest baselineToken baselineAccepted
      candidateSatDigest candidateUnsatDigest candidateToken)
    (AyRejectedBisectReport
      baselineSatDigest baselineUnsatDigest
      candidateSatDigest candidateUnsatDigest
      baselineToken candidateToken rejected)

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

theorem ay_accepted_report_replay
    (baselineSatDigest : Prop) (baselineUnsatDigest : Prop)
    (baselineToken : Prop) (baselineAccepted : Prop)
    (candidateSatDigest : Prop) (candidateUnsatDigest : Prop)
    (candidateToken : Prop) :
    AyAcceptedBisectReport
      baselineSatDigest baselineUnsatDigest baselineToken baselineAccepted
      candidateSatDigest candidateUnsatDigest candidateToken ->
    AyAuditReplay baselineAccepted := by
  intro report
  exact ay_conj_left
    (AyAuditReplay baselineAccepted)
    (AyConj
      (AyPublicOutputComparison baselineToken candidateToken)
      (AyConj
        (AyArtifactDigestDiagnostic baselineSatDigest baselineUnsatDigest)
        (AyArtifactDigestDiagnostic candidateSatDigest candidateUnsatDigest)))
    report

theorem ay_public_output_comparison_forward
    (baselineToken : Prop) (candidateToken : Prop) :
    AyPublicOutputComparison baselineToken candidateToken ->
    baselineToken ->
    candidateToken := by
  intro comparison
  exact ay_equisat_forward baselineToken candidateToken comparison

theorem ay_digest_diagnostic_sat
    (satDigest : Prop) (unsatDigest : Prop) :
    satDigest ->
    AyArtifactDigestDiagnostic satDigest unsatDigest := by
  intro sat_digest
  exact ay_disj_left satDigest unsatDigest sat_digest

theorem ay_digest_diagnostic_unsat
    (satDigest : Prop) (unsatDigest : Prop) :
    unsatDigest ->
    AyArtifactDigestDiagnostic satDigest unsatDigest := by
  intro unsat_digest
  exact ay_disj_right satDigest unsatDigest unsat_digest

theorem ay_accepted_report_preserves_baseline_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineSatDigest : Prop) (baselineUnsatDigest : Prop)
    (baselineToken : Prop) (baselineAccepted : Prop)
    (candidateSatDigest : Prop) (candidateUnsatDigest : Prop)
    (candidateToken : Prop) :
    AyAcceptedBisectReport
      baselineSatDigest baselineUnsatDigest baselineToken baselineAccepted
      candidateSatDigest candidateUnsatDigest candidateToken ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineSatDigest baselineUnsatDigest baselineToken baselineAccepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro report
  intro baseline_manifest
  exact ay_manifest_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    baselineSatDigest baselineUnsatDigest baselineToken baselineAccepted
    baseline_manifest
    (ay_accepted_report_replay
      baselineSatDigest baselineUnsatDigest baselineToken baselineAccepted
      candidateSatDigest candidateUnsatDigest candidateToken report)

theorem ay_rejected_report_exposes_diagnostics
    (baselineSatDigest : Prop) (baselineUnsatDigest : Prop)
    (candidateSatDigest : Prop) (candidateUnsatDigest : Prop)
    (baselineToken : Prop) (candidateToken : Prop) (rejected : Prop) :
    AyRejectedBisectReport
      baselineSatDigest baselineUnsatDigest
      candidateSatDigest candidateUnsatDigest
      baselineToken candidateToken rejected ->
    AyBisectRejected rejected := by
  intro report
  exact ay_conj_left
    (AyBisectRejected rejected)
    (AyConj
      (AyArtifactDigestDiagnostic baselineSatDigest baselineUnsatDigest)
      (AyConj
        (AyArtifactDigestDiagnostic candidateSatDigest candidateUnsatDigest)
        (AyPublicOutputComparison baselineToken candidateToken)))
    report

theorem ay_rejected_report_no_claim
    (baselineSatDigest : Prop) (baselineUnsatDigest : Prop)
    (baselineToken : Prop) (baselineAccepted : Prop)
    (candidateSatDigest : Prop) (candidateUnsatDigest : Prop)
    (candidateToken : Prop) (rejected : Prop) :
    AyRejectedBisectReport
      baselineSatDigest baselineUnsatDigest
      candidateSatDigest candidateUnsatDigest
      baselineToken candidateToken rejected ->
    AyBisectReport
      baselineSatDigest baselineUnsatDigest baselineToken baselineAccepted
      candidateSatDigest candidateUnsatDigest candidateToken rejected := by
  intro report
  exact ay_disj_right
    (AyAcceptedBisectReport
      baselineSatDigest baselineUnsatDigest baselineToken baselineAccepted
      candidateSatDigest candidateUnsatDigest candidateToken)
    (AyRejectedBisectReport
      baselineSatDigest baselineUnsatDigest
      candidateSatDigest candidateUnsatDigest
      baselineToken candidateToken rejected)
    report

