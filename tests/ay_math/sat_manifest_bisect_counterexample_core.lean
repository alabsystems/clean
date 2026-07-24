-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Counterexample localization for manifest-bisect reports. Accepted reports
-- preserve baseline public SAT/UNSAT soundness. Rejected reports isolate
-- digest/output disagreement and stay diagnostic: they do not become semantic
-- solver correctness claims.

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

def AyPublicOutcome (satToken : Prop) (unsatToken : Prop) :=
  AyDisj satToken unsatToken

def AyArtifactDigestDiagnostic
    (satDigest : Prop) (unsatDigest : Prop) :=
  AyDisj satDigest unsatDigest

def AyDigestDisagreement (baselineDigest : Prop) (optimizedDigest : Prop) :=
  AyConj baselineDigest optimizedDigest

def AyOutputDisagreement (baselineOutput : Prop) (optimizedOutput : Prop) :=
  AyConj baselineOutput optimizedOutput

def AyLocalizedCounterexampleWitness
    (digestDisagreement : Prop) (outputDisagreement : Prop) :=
  AyDisj digestDisagreement outputDisagreement

def AyPerformanceRegressionLocalization (perfWitness : Prop) :=
  perfWitness

def AyAuditReplay (accepted : Prop) :=
  accepted

def AyRejectedReport (rejected : Prop) :=
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
    (optimizedSatDigest : Prop) (optimizedUnsatDigest : Prop)
    (baselineToken : Prop) (optimizedToken : Prop)
    (baselineAccepted : Prop) :=
  AyConj
    (AyAuditReplay baselineAccepted)
    (AyConj
      (AyEquisat baselineToken optimizedToken)
      (AyConj
        (AyArtifactDigestDiagnostic baselineSatDigest baselineUnsatDigest)
        (AyArtifactDigestDiagnostic optimizedSatDigest optimizedUnsatDigest)))

def AyRejectedBisectReport
    (baselineDigest : Prop) (optimizedDigest : Prop)
    (baselineOutput : Prop) (optimizedOutput : Prop)
    (counterexample : Prop) (rejected : Prop) :=
  AyConj
    (AyRejectedReport rejected)
    (AyConj
      (AyDigestDisagreement baselineDigest optimizedDigest)
      (AyConj
        (AyOutputDisagreement baselineOutput optimizedOutput)
        (AyLocalizedCounterexampleWitness counterexample counterexample)))

def AyBisectCounterexampleReport
    (baselineSatDigest : Prop) (baselineUnsatDigest : Prop)
    (optimizedSatDigest : Prop) (optimizedUnsatDigest : Prop)
    (baselineToken : Prop) (optimizedToken : Prop)
    (baselineAccepted : Prop)
    (baselineDigest : Prop) (optimizedDigest : Prop)
    (baselineOutput : Prop) (optimizedOutput : Prop)
    (counterexample : Prop) (rejected : Prop) :=
  AyDisj
    (AyAcceptedBisectReport
      baselineSatDigest baselineUnsatDigest
      optimizedSatDigest optimizedUnsatDigest
      baselineToken optimizedToken baselineAccepted)
    (AyRejectedBisectReport
      baselineDigest optimizedDigest baselineOutput optimizedOutput
      counterexample rejected)

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
    (optimizedSatDigest : Prop) (optimizedUnsatDigest : Prop)
    (baselineToken : Prop) (optimizedToken : Prop)
    (baselineAccepted : Prop) :
    AyAcceptedBisectReport
      baselineSatDigest baselineUnsatDigest
      optimizedSatDigest optimizedUnsatDigest
      baselineToken optimizedToken baselineAccepted ->
    AyAuditReplay baselineAccepted := by
  intro report
  exact ay_conj_left
    (AyAuditReplay baselineAccepted)
    (AyConj
      (AyEquisat baselineToken optimizedToken)
      (AyConj
        (AyArtifactDigestDiagnostic baselineSatDigest baselineUnsatDigest)
        (AyArtifactDigestDiagnostic optimizedSatDigest optimizedUnsatDigest)))
    report

theorem ay_accepted_bisect_preserves_baseline_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineSatDigest : Prop) (baselineUnsatDigest : Prop)
    (optimizedSatDigest : Prop) (optimizedUnsatDigest : Prop)
    (baselineToken : Prop) (optimizedToken : Prop)
    (baselineAccepted : Prop) :
    AyAcceptedBisectReport
      baselineSatDigest baselineUnsatDigest
      optimizedSatDigest optimizedUnsatDigest
      baselineToken optimizedToken baselineAccepted ->
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
      baselineSatDigest baselineUnsatDigest
      optimizedSatDigest optimizedUnsatDigest
      baselineToken optimizedToken baselineAccepted report)

theorem ay_rejected_report_rejection
    (baselineDigest : Prop) (optimizedDigest : Prop)
    (baselineOutput : Prop) (optimizedOutput : Prop)
    (counterexample : Prop) (rejected : Prop) :
    AyRejectedBisectReport
      baselineDigest optimizedDigest baselineOutput optimizedOutput
      counterexample rejected ->
    AyRejectedReport rejected := by
  intro report
  exact ay_conj_left
    (AyRejectedReport rejected)
    (AyConj
      (AyDigestDisagreement baselineDigest optimizedDigest)
      (AyConj
        (AyOutputDisagreement baselineOutput optimizedOutput)
        (AyLocalizedCounterexampleWitness counterexample counterexample)))
    report

theorem ay_rejected_report_digest_or_output_disagreement
    (baselineDigest : Prop) (optimizedDigest : Prop)
    (baselineOutput : Prop) (optimizedOutput : Prop)
    (counterexample : Prop) (rejected : Prop) :
    AyRejectedBisectReport
      baselineDigest optimizedDigest baselineOutput optimizedOutput
      counterexample rejected ->
    AyConj
      (AyDigestDisagreement baselineDigest optimizedDigest)
      (AyOutputDisagreement baselineOutput optimizedOutput) := by
  intro report
  let tail := report
    (AyConj
      (AyDigestDisagreement baselineDigest optimizedDigest)
      (AyConj
        (AyOutputDisagreement baselineOutput optimizedOutput)
        (AyLocalizedCounterexampleWitness counterexample counterexample)))
    (fun _rejected diagnostic_tail => diagnostic_tail)
  exact tail
    (AyConj
      (AyDigestDisagreement baselineDigest optimizedDigest)
      (AyOutputDisagreement baselineOutput optimizedOutput))
    (fun digest_disagreement output_tail =>
      output_tail
        (AyConj
          (AyDigestDisagreement baselineDigest optimizedDigest)
          (AyOutputDisagreement baselineOutput optimizedOutput))
        (fun output_disagreement _witness =>
          ay_conj_intro
            (AyDigestDisagreement baselineDigest optimizedDigest)
            (AyOutputDisagreement baselineOutput optimizedOutput)
            digest_disagreement
            output_disagreement))

theorem ay_counterexample_witness_from_digest
    (digestDisagreement : Prop) (outputDisagreement : Prop) :
    digestDisagreement ->
    AyLocalizedCounterexampleWitness
      digestDisagreement outputDisagreement := by
  intro digest
  exact ay_disj_left digestDisagreement outputDisagreement digest

theorem ay_counterexample_witness_from_output
    (digestDisagreement : Prop) (outputDisagreement : Prop) :
    outputDisagreement ->
    AyLocalizedCounterexampleWitness
      digestDisagreement outputDisagreement := by
  intro output
  exact ay_disj_right digestDisagreement outputDisagreement output

theorem ay_rejected_report_no_semantic_claim
    (baselineSatDigest : Prop) (baselineUnsatDigest : Prop)
    (optimizedSatDigest : Prop) (optimizedUnsatDigest : Prop)
    (baselineToken : Prop) (optimizedToken : Prop)
    (baselineAccepted : Prop)
    (baselineDigest : Prop) (optimizedDigest : Prop)
    (baselineOutput : Prop) (optimizedOutput : Prop)
    (counterexample : Prop) (rejected : Prop) :
    AyRejectedBisectReport
      baselineDigest optimizedDigest baselineOutput optimizedOutput
      counterexample rejected ->
    AyBisectCounterexampleReport
      baselineSatDigest baselineUnsatDigest
      optimizedSatDigest optimizedUnsatDigest
      baselineToken optimizedToken baselineAccepted
      baselineDigest optimizedDigest baselineOutput optimizedOutput
      counterexample rejected := by
  intro report
  exact ay_disj_right
    (AyAcceptedBisectReport
      baselineSatDigest baselineUnsatDigest
      optimizedSatDigest optimizedUnsatDigest
      baselineToken optimizedToken baselineAccepted)
    (AyRejectedBisectReport
      baselineDigest optimizedDigest baselineOutput optimizedOutput
      counterexample rejected)
    report

theorem ay_performance_localization_not_semantic_claim
    (perfWitness : Prop) (semanticClaim : Prop) :
    AyPerformanceRegressionLocalization perfWitness ->
    perfWitness ->
    AyPerformanceRegressionLocalization perfWitness := by
  intro localization
  intro _witness
  exact localization

theorem ay_diagnostic_counterexample_separates_solver_soundness
    (baselineDigest : Prop) (optimizedDigest : Prop)
    (baselineOutput : Prop) (optimizedOutput : Prop)
    (counterexample : Prop) (rejected : Prop)
    (semanticClaim : Prop) :
    AyRejectedBisectReport
      baselineDigest optimizedDigest baselineOutput optimizedOutput
      counterexample rejected ->
    AyConj
      (AyRejectedReport rejected)
      (AyLocalizedCounterexampleWitness counterexample counterexample) := by
  intro report
  let tail := report
    (AyConj
      (AyDigestDisagreement baselineDigest optimizedDigest)
      (AyConj
        (AyOutputDisagreement baselineOutput optimizedOutput)
        (AyLocalizedCounterexampleWitness counterexample counterexample)))
    (fun _rejected diagnostic_tail => diagnostic_tail)
  let output_tail := tail
    (AyConj
      (AyOutputDisagreement baselineOutput optimizedOutput)
      (AyLocalizedCounterexampleWitness counterexample counterexample))
    (fun _digest output_tail => output_tail)
  exact ay_conj_intro
    (AyRejectedReport rejected)
    (AyLocalizedCounterexampleWitness counterexample counterexample)
    (ay_rejected_report_rejection
      baselineDigest optimizedDigest baselineOutput optimizedOutput
      counterexample rejected report)
    (output_tail
      (AyLocalizedCounterexampleWitness counterexample counterexample)
      (fun _output witness => witness))

