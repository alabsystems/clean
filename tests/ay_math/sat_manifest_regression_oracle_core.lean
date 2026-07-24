-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Regression oracle core for ay SAT-COMP manifests. The oracle compares a
-- baseline manifest with a candidate manifest through artifact keys, branch
-- digests, public output tokens, and replay evidence.

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

def AyArtifactKeys (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :=
  AyConj satKey (AyConj unsatKey outcomeKey)

def AyArtifactDigests (satDigest : Prop) (unsatDigest : Prop) :=
  AyDisj satDigest unsatDigest

def AyPublicOutputComparison
    (baselineToken : Prop) (candidateToken : Prop) :=
  AyEquisat baselineToken candidateToken

def AyAuditReplay (accepted : Prop) :=
  accepted

def AyRegressionRejected (rejected : Prop) :=
  rejected

def AyCertificateArchive
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :=
  AyConj
    (satKey -> AySatArtifact visibleModel originalModel)
    (AyConj
      (unsatKey ->
        AyUnsatArtifact originalFormula visibleFormula finalClause)
      (outcomeKey ->
        AyCompressedOutcome
          originalFormula visibleFormula visibleModel originalModel
          finalClause))

def AyRunManifest
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop)
    (satDigest : Prop) (unsatDigest : Prop) (publicToken : Prop)
    (accepted : Prop) :=
  AyConj
    (AyArtifactKeys satKey unsatKey outcomeKey)
    (AyConj
      (AyArtifactDigests satDigest unsatDigest)
      (AyConj
        publicToken
        (AyConj
          (AyAuditReplay accepted)
          (accepted ->
            AyCompressedOutcome
              originalFormula visibleFormula visibleModel originalModel
              finalClause))))

def AyOracleAccepted
    (baselineSatKey : Prop) (baselineUnsatKey : Prop)
    (baselineOutcomeKey : Prop) (baselineSatDigest : Prop)
    (baselineUnsatDigest : Prop) (baselineToken : Prop)
    (candidateSatKey : Prop) (candidateUnsatKey : Prop)
    (candidateOutcomeKey : Prop) (candidateSatDigest : Prop)
    (candidateUnsatDigest : Prop) (candidateToken : Prop)
    (candidateAccepted : Prop) :=
  AyConj
    (AyEquisat baselineSatKey candidateSatKey)
    (AyConj
      (AyEquisat baselineUnsatKey candidateUnsatKey)
      (AyConj
        (AyEquisat baselineOutcomeKey candidateOutcomeKey)
        (AyConj
          (AyEquisat baselineSatDigest candidateSatDigest)
          (AyConj
            (AyEquisat baselineUnsatDigest candidateUnsatDigest)
            (AyConj
              (AyPublicOutputComparison baselineToken candidateToken)
              (AyAuditReplay candidateAccepted))))))

def AyRegressionOracle
    (baselineSatKey : Prop) (baselineUnsatKey : Prop)
    (baselineOutcomeKey : Prop) (baselineSatDigest : Prop)
    (baselineUnsatDigest : Prop) (baselineToken : Prop)
    (candidateSatKey : Prop) (candidateUnsatKey : Prop)
    (candidateOutcomeKey : Prop) (candidateSatDigest : Prop)
    (candidateUnsatDigest : Prop) (candidateToken : Prop)
    (candidateAccepted : Prop) (rejected : Prop) :=
  AyDisj
    (AyOracleAccepted
      baselineSatKey baselineUnsatKey baselineOutcomeKey
      baselineSatDigest baselineUnsatDigest baselineToken
      candidateSatKey candidateUnsatKey candidateOutcomeKey
      candidateSatDigest candidateUnsatDigest candidateToken
      candidateAccepted)
    (AyRegressionRejected rejected)

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

theorem ay_archive_sat_lookup
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    satKey ->
    AySatArtifact visibleModel originalModel := by
  intro archive
  exact ay_conj_left
    (satKey -> AySatArtifact visibleModel originalModel)
    (AyConj
      (unsatKey ->
        AyUnsatArtifact originalFormula visibleFormula finalClause)
      (outcomeKey ->
        AyCompressedOutcome
          originalFormula visibleFormula visibleModel originalModel
          finalClause))
    archive

theorem ay_archive_unsat_lookup
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    unsatKey ->
    AyUnsatArtifact originalFormula visibleFormula finalClause := by
  intro archive
  let tail := archive
    (AyConj
      (unsatKey ->
        AyUnsatArtifact originalFormula visibleFormula finalClause)
      (outcomeKey ->
        AyCompressedOutcome
          originalFormula visibleFormula visibleModel originalModel
          finalClause))
    (fun _sat_lookup archive_tail => archive_tail)
  exact ay_conj_left
    (unsatKey ->
      AyUnsatArtifact originalFormula visibleFormula finalClause)
    (outcomeKey ->
      AyCompressedOutcome
        originalFormula visibleFormula visibleModel originalModel finalClause)
    tail

theorem ay_archive_outcome_lookup
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey ->
    outcomeKey ->
    AyCompressedOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  intro archive
  let tail := archive
    (AyConj
      (unsatKey ->
        AyUnsatArtifact originalFormula visibleFormula finalClause)
      (outcomeKey ->
        AyCompressedOutcome
          originalFormula visibleFormula visibleModel originalModel
          finalClause))
    (fun _sat_lookup archive_tail => archive_tail)
  exact tail
    (outcomeKey ->
      AyCompressedOutcome
        originalFormula visibleFormula visibleModel originalModel finalClause)
    (fun _unsat_lookup outcome_lookup => outcome_lookup)

theorem ay_manifest_replay_outcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop)
    (satDigest : Prop) (unsatDigest : Prop) (publicToken : Prop)
    (accepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey satDigest unsatDigest publicToken accepted ->
    accepted ->
    AyCompressedOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  intro manifest
  let tail1 := manifest
    (AyConj
      (AyArtifactDigests satDigest unsatDigest)
      (AyConj
        publicToken
        (AyConj
          (AyAuditReplay accepted)
          (accepted ->
            AyCompressedOutcome
              originalFormula visibleFormula visibleModel originalModel
              finalClause))))
    (fun _keys manifest_tail => manifest_tail)
  let tail2 := tail1
    (AyConj
      publicToken
      (AyConj
        (AyAuditReplay accepted)
        (accepted ->
          AyCompressedOutcome
            originalFormula visibleFormula visibleModel originalModel
            finalClause)))
    (fun _digests manifest_tail => manifest_tail)
  let tail3 := tail2
    (AyConj
      (AyAuditReplay accepted)
      (accepted ->
        AyCompressedOutcome
          originalFormula visibleFormula visibleModel originalModel
          finalClause))
    (fun _token manifest_tail => manifest_tail)
  exact tail3
    (accepted ->
      AyCompressedOutcome
        originalFormula visibleFormula visibleModel originalModel finalClause)
    (fun _decision replay => replay)

theorem ay_manifest_public_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop)
    (satDigest : Prop) (unsatDigest : Prop) (publicToken : Prop)
    (accepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey satDigest unsatDigest publicToken accepted ->
    accepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro manifest
  intro accepted_h
  exact ay_outcome_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    (ay_manifest_replay_outcome
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey satDigest unsatDigest publicToken accepted
      manifest accepted_h)

theorem ay_oracle_sat_key_match
    (baselineSatKey : Prop) (baselineUnsatKey : Prop)
    (baselineOutcomeKey : Prop) (baselineSatDigest : Prop)
    (baselineUnsatDigest : Prop) (baselineToken : Prop)
    (candidateSatKey : Prop) (candidateUnsatKey : Prop)
    (candidateOutcomeKey : Prop) (candidateSatDigest : Prop)
    (candidateUnsatDigest : Prop) (candidateToken : Prop)
    (candidateAccepted : Prop) :
    AyOracleAccepted
      baselineSatKey baselineUnsatKey baselineOutcomeKey
      baselineSatDigest baselineUnsatDigest baselineToken
      candidateSatKey candidateUnsatKey candidateOutcomeKey
      candidateSatDigest candidateUnsatDigest candidateToken
      candidateAccepted ->
    AyEquisat baselineSatKey candidateSatKey := by
  intro accepted
  exact ay_conj_left
    (AyEquisat baselineSatKey candidateSatKey)
    (AyConj
      (AyEquisat baselineUnsatKey candidateUnsatKey)
      (AyConj
        (AyEquisat baselineOutcomeKey candidateOutcomeKey)
        (AyConj
          (AyEquisat baselineSatDigest candidateSatDigest)
          (AyConj
            (AyEquisat baselineUnsatDigest candidateUnsatDigest)
            (AyConj
              (AyPublicOutputComparison baselineToken candidateToken)
              (AyAuditReplay candidateAccepted))))))
    accepted

theorem ay_oracle_candidate_replay
    (baselineSatKey : Prop) (baselineUnsatKey : Prop)
    (baselineOutcomeKey : Prop) (baselineSatDigest : Prop)
    (baselineUnsatDigest : Prop) (baselineToken : Prop)
    (candidateSatKey : Prop) (candidateUnsatKey : Prop)
    (candidateOutcomeKey : Prop) (candidateSatDigest : Prop)
    (candidateUnsatDigest : Prop) (candidateToken : Prop)
    (candidateAccepted : Prop) :
    AyOracleAccepted
      baselineSatKey baselineUnsatKey baselineOutcomeKey
      baselineSatDigest baselineUnsatDigest baselineToken
      candidateSatKey candidateUnsatKey candidateOutcomeKey
      candidateSatDigest candidateUnsatDigest candidateToken
      candidateAccepted ->
    AyAuditReplay candidateAccepted := by
  intro accepted
  let tail1 := accepted
    (AyConj
      (AyEquisat baselineUnsatKey candidateUnsatKey)
      (AyConj
        (AyEquisat baselineOutcomeKey candidateOutcomeKey)
        (AyConj
          (AyEquisat baselineSatDigest candidateSatDigest)
          (AyConj
            (AyEquisat baselineUnsatDigest candidateUnsatDigest)
            (AyConj
              (AyPublicOutputComparison baselineToken candidateToken)
              (AyAuditReplay candidateAccepted))))))
    (fun _sat_key tail => tail)
  let tail2 := tail1
    (AyConj
      (AyEquisat baselineOutcomeKey candidateOutcomeKey)
      (AyConj
        (AyEquisat baselineSatDigest candidateSatDigest)
        (AyConj
          (AyEquisat baselineUnsatDigest candidateUnsatDigest)
          (AyConj
            (AyPublicOutputComparison baselineToken candidateToken)
            (AyAuditReplay candidateAccepted)))))
    (fun _unsat_key tail => tail)
  let tail3 := tail2
    (AyConj
      (AyEquisat baselineSatDigest candidateSatDigest)
      (AyConj
        (AyEquisat baselineUnsatDigest candidateUnsatDigest)
        (AyConj
          (AyPublicOutputComparison baselineToken candidateToken)
          (AyAuditReplay candidateAccepted))))
    (fun _outcome_key tail => tail)
  let tail4 := tail3
    (AyConj
      (AyEquisat baselineUnsatDigest candidateUnsatDigest)
      (AyConj
        (AyPublicOutputComparison baselineToken candidateToken)
        (AyAuditReplay candidateAccepted)))
    (fun _sat_digest tail => tail)
  let tail5 := tail4
    (AyConj
      (AyPublicOutputComparison baselineToken candidateToken)
      (AyAuditReplay candidateAccepted))
    (fun _unsat_digest tail => tail)
  exact tail5
    (AyAuditReplay candidateAccepted)
    (fun _token_cmp replay => replay)

theorem ay_oracle_matching_sat_artifact
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineSatKey : Prop) (candidateSatKey : Prop)
    (candidateUnsatKey : Prop) (candidateOutcomeKey : Prop) :
    AyEquisat baselineSatKey candidateSatKey ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      candidateSatKey candidateUnsatKey candidateOutcomeKey ->
    baselineSatKey ->
    AySatArtifact visibleModel originalModel := by
  intro key_match
  intro candidate_archive
  intro baseline_key
  exact ay_archive_sat_lookup
    originalFormula visibleFormula visibleModel originalModel finalClause
    candidateSatKey candidateUnsatKey candidateOutcomeKey
    candidate_archive
    (ay_equisat_forward baselineSatKey candidateSatKey
      key_match baseline_key)

theorem ay_oracle_matching_unsat_artifact
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (candidateSatKey : Prop) (baselineUnsatKey : Prop)
    (candidateUnsatKey : Prop) (candidateOutcomeKey : Prop) :
    AyEquisat baselineUnsatKey candidateUnsatKey ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      candidateSatKey candidateUnsatKey candidateOutcomeKey ->
    baselineUnsatKey ->
    AyUnsatArtifact originalFormula visibleFormula finalClause := by
  intro key_match
  intro candidate_archive
  intro baseline_key
  exact ay_archive_unsat_lookup
    originalFormula visibleFormula visibleModel originalModel finalClause
    candidateSatKey candidateUnsatKey candidateOutcomeKey
    candidate_archive
    (ay_equisat_forward baselineUnsatKey candidateUnsatKey
      key_match baseline_key)

theorem ay_oracle_matching_outcome_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (candidateSatKey : Prop) (candidateUnsatKey : Prop)
    (baselineOutcomeKey : Prop) (candidateOutcomeKey : Prop) :
    AyEquisat baselineOutcomeKey candidateOutcomeKey ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      candidateSatKey candidateUnsatKey candidateOutcomeKey ->
    baselineOutcomeKey ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro key_match
  intro candidate_archive
  intro baseline_key
  exact ay_outcome_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    (ay_archive_outcome_lookup
      originalFormula visibleFormula visibleModel originalModel finalClause
      candidateSatKey candidateUnsatKey candidateOutcomeKey
      candidate_archive
      (ay_equisat_forward baselineOutcomeKey candidateOutcomeKey
        key_match baseline_key))

theorem ay_oracle_accepts_candidate_public_soundness
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (candidateSatKey : Prop) (candidateUnsatKey : Prop)
    (candidateOutcomeKey : Prop) (candidateSatDigest : Prop)
    (candidateUnsatDigest : Prop) (candidateToken : Prop)
    (candidateAccepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      candidateSatKey candidateUnsatKey candidateOutcomeKey
      candidateSatDigest candidateUnsatDigest candidateToken
      candidateAccepted ->
    AyAuditReplay candidateAccepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro candidate_manifest
  intro accepted
  exact ay_manifest_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    candidateSatKey candidateUnsatKey candidateOutcomeKey
    candidateSatDigest candidateUnsatDigest candidateToken
    candidateAccepted candidate_manifest accepted

theorem ay_oracle_candidate_same_public_theorem_as_baseline
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (baselineSatKey : Prop) (baselineUnsatKey : Prop)
    (baselineOutcomeKey : Prop) (baselineSatDigest : Prop)
    (baselineUnsatDigest : Prop) (baselineToken : Prop)
    (baselineAccepted : Prop)
    (candidateSatKey : Prop) (candidateUnsatKey : Prop)
    (candidateOutcomeKey : Prop) (candidateSatDigest : Prop)
    (candidateUnsatDigest : Prop) (candidateToken : Prop)
    (candidateAccepted : Prop) :
    AyOracleAccepted
      baselineSatKey baselineUnsatKey baselineOutcomeKey
      baselineSatDigest baselineUnsatDigest baselineToken
      candidateSatKey candidateUnsatKey candidateOutcomeKey
      candidateSatDigest candidateUnsatDigest candidateToken
      candidateAccepted ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineSatKey baselineUnsatKey baselineOutcomeKey
      baselineSatDigest baselineUnsatDigest baselineToken baselineAccepted ->
    baselineAccepted ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      candidateSatKey candidateUnsatKey candidateOutcomeKey
      candidateSatDigest candidateUnsatDigest candidateToken
      candidateAccepted ->
    AyConj
      (AyPublicSoundnessTheorem originalFormula originalModel)
      (AyPublicSoundnessTheorem originalFormula originalModel) := by
  intro oracle_accept
  intro baseline_manifest
  intro baseline_accepted
  intro candidate_manifest
  exact ay_conj_intro
    (AyPublicSoundnessTheorem originalFormula originalModel)
    (AyPublicSoundnessTheorem originalFormula originalModel)
    (ay_manifest_public_soundness
      originalFormula visibleFormula visibleModel originalModel finalClause
      baselineSatKey baselineUnsatKey baselineOutcomeKey
      baselineSatDigest baselineUnsatDigest baselineToken baselineAccepted
      baseline_manifest baseline_accepted)
    (ay_oracle_accepts_candidate_public_soundness
      originalFormula visibleFormula visibleModel originalModel finalClause
      candidateSatKey candidateUnsatKey candidateOutcomeKey
      candidateSatDigest candidateUnsatDigest candidateToken
      candidateAccepted candidate_manifest
      (ay_oracle_candidate_replay
        baselineSatKey baselineUnsatKey baselineOutcomeKey
        baselineSatDigest baselineUnsatDigest baselineToken
        candidateSatKey candidateUnsatKey candidateOutcomeKey
        candidateSatDigest candidateUnsatDigest candidateToken
        candidateAccepted oracle_accept))

theorem ay_oracle_rejects_no_semantic_claim
    (rejected : Prop)
    (semanticClaim : Prop) :
    AyRegressionRejected rejected ->
    AyRegressionOracle
      semanticClaim semanticClaim semanticClaim semanticClaim semanticClaim
      semanticClaim semanticClaim semanticClaim semanticClaim semanticClaim
      semanticClaim semanticClaim semanticClaim rejected := by
  intro rejected_h
  exact ay_disj_right
    (AyOracleAccepted
      semanticClaim semanticClaim semanticClaim semanticClaim semanticClaim
      semanticClaim semanticClaim semanticClaim semanticClaim semanticClaim
      semanticClaim semanticClaim semanticClaim)
    (AyRegressionRejected rejected)
    rejected_h

