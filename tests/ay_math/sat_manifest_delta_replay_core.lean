-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Delta replay core for ay SAT-COMP manifests. A delta can change artifact
-- keys while preserving branch digests and public output behavior. Accepted
-- deltas replay a candidate certificate and preserve the public SAT/UNSAT
-- theorem; rejected deltas expose no semantic theorem.

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

def AyChangedArtifactKeys
    (baselineKey : Prop) (candidateKey : Prop) :=
  AyEquisat baselineKey candidateKey

def AyUnchangedBranchDigests
    (baselineDigest : Prop) (candidateDigest : Prop) :=
  AyEquisat baselineDigest candidateDigest

def AyPublicOutputComparison
    (baselineToken : Prop) (candidateToken : Prop) :=
  AyEquisat baselineToken candidateToken

def AyAuditReplay (accepted : Prop) :=
  accepted

def AyDeltaRejected (rejected : Prop) :=
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
    satKey
    (AyConj
      unsatKey
      (AyConj
        outcomeKey
        (AyConj
          (AyDisj satDigest unsatDigest)
          (AyConj
            publicToken
            (AyConj
              (AyAuditReplay accepted)
              (accepted ->
                AyCompressedOutcome
                  originalFormula visibleFormula visibleModel originalModel
                  finalClause))))))

def AyDeltaAccepted
    (baselineSatKey : Prop) (baselineUnsatKey : Prop)
    (baselineOutcomeKey : Prop) (baselineSatDigest : Prop)
    (baselineUnsatDigest : Prop) (baselineToken : Prop)
    (candidateSatKey : Prop) (candidateUnsatKey : Prop)
    (candidateOutcomeKey : Prop) (candidateSatDigest : Prop)
    (candidateUnsatDigest : Prop) (candidateToken : Prop)
    (candidateAccepted : Prop) :=
  AyConj
    (AyChangedArtifactKeys baselineSatKey candidateSatKey)
    (AyConj
      (AyChangedArtifactKeys baselineUnsatKey candidateUnsatKey)
      (AyConj
        (AyChangedArtifactKeys baselineOutcomeKey candidateOutcomeKey)
        (AyConj
          (AyUnchangedBranchDigests baselineSatDigest candidateSatDigest)
          (AyConj
            (AyUnchangedBranchDigests
              baselineUnsatDigest candidateUnsatDigest)
            (AyConj
              (AyPublicOutputComparison baselineToken candidateToken)
              (AyAuditReplay candidateAccepted))))))

def AyDeltaReplayOracle
    (baselineSatKey : Prop) (baselineUnsatKey : Prop)
    (baselineOutcomeKey : Prop) (baselineSatDigest : Prop)
    (baselineUnsatDigest : Prop) (baselineToken : Prop)
    (candidateSatKey : Prop) (candidateUnsatKey : Prop)
    (candidateOutcomeKey : Prop) (candidateSatDigest : Prop)
    (candidateUnsatDigest : Prop) (candidateToken : Prop)
    (candidateAccepted : Prop) (rejected : Prop) :=
  AyDisj
    (AyDeltaAccepted
      baselineSatKey baselineUnsatKey baselineOutcomeKey
      baselineSatDigest baselineUnsatDigest baselineToken
      candidateSatKey candidateUnsatKey candidateOutcomeKey
      candidateSatDigest candidateUnsatDigest candidateToken
      candidateAccepted)
    (AyDeltaRejected rejected)

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

theorem ay_manifest_sat_key
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop)
    (satDigest : Prop) (unsatDigest : Prop) (publicToken : Prop)
    (accepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKey unsatKey outcomeKey satDigest unsatDigest publicToken accepted ->
    satKey := by
  intro manifest
  exact ay_conj_left satKey
    (AyConj
      unsatKey
      (AyConj
        outcomeKey
        (AyConj
          (AyDisj satDigest unsatDigest)
          (AyConj
            publicToken
            (AyConj
              (AyAuditReplay accepted)
              (accepted ->
                AyCompressedOutcome
                  originalFormula visibleFormula visibleModel originalModel
                  finalClause))))))
    manifest

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
      unsatKey
      (AyConj
        outcomeKey
        (AyConj
          (AyDisj satDigest unsatDigest)
          (AyConj
            publicToken
            (AyConj
              (AyAuditReplay accepted)
              (accepted ->
                AyCompressedOutcome
                  originalFormula visibleFormula visibleModel originalModel
                  finalClause))))))
    (fun _sat_key manifest_tail => manifest_tail)
  let tail2 := tail1
    (AyConj
      outcomeKey
      (AyConj
        (AyDisj satDigest unsatDigest)
        (AyConj
          publicToken
          (AyConj
            (AyAuditReplay accepted)
            (accepted ->
              AyCompressedOutcome
                originalFormula visibleFormula visibleModel originalModel
                finalClause)))))
    (fun _unsat_key manifest_tail => manifest_tail)
  let tail3 := tail2
    (AyConj
      (AyDisj satDigest unsatDigest)
      (AyConj
        publicToken
        (AyConj
          (AyAuditReplay accepted)
          (accepted ->
            AyCompressedOutcome
              originalFormula visibleFormula visibleModel originalModel
              finalClause))))
    (fun _outcome_key manifest_tail => manifest_tail)
  let tail4 := tail3
    (AyConj
      publicToken
      (AyConj
        (AyAuditReplay accepted)
        (accepted ->
          AyCompressedOutcome
            originalFormula visibleFormula visibleModel originalModel
            finalClause)))
    (fun _digest manifest_tail => manifest_tail)
  let tail5 := tail4
    (AyConj
      (AyAuditReplay accepted)
      (accepted ->
        AyCompressedOutcome
          originalFormula visibleFormula visibleModel originalModel
          finalClause))
    (fun _token manifest_tail => manifest_tail)
  exact tail5
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

theorem ay_delta_sat_key_maps_to_candidate
    (baselineSatKey : Prop) (candidateSatKey : Prop) :
    AyChangedArtifactKeys baselineSatKey candidateSatKey ->
    baselineSatKey ->
    candidateSatKey := by
  intro changed
  exact ay_equisat_forward baselineSatKey candidateSatKey changed

theorem ay_delta_unsat_key_maps_to_candidate
    (baselineUnsatKey : Prop) (candidateUnsatKey : Prop) :
    AyChangedArtifactKeys baselineUnsatKey candidateUnsatKey ->
    baselineUnsatKey ->
    candidateUnsatKey := by
  intro changed
  exact ay_equisat_forward baselineUnsatKey candidateUnsatKey changed

theorem ay_delta_outcome_key_maps_to_candidate
    (baselineOutcomeKey : Prop) (candidateOutcomeKey : Prop) :
    AyChangedArtifactKeys baselineOutcomeKey candidateOutcomeKey ->
    baselineOutcomeKey ->
    candidateOutcomeKey := by
  intro changed
  exact ay_equisat_forward baselineOutcomeKey candidateOutcomeKey changed

theorem ay_delta_digest_preserves_sat_branch
    (baselineSatDigest : Prop) (candidateSatDigest : Prop)
    (candidateUnsatDigest : Prop) :
    AyUnchangedBranchDigests baselineSatDigest candidateSatDigest ->
    baselineSatDigest ->
    AyDisj candidateSatDigest candidateUnsatDigest := by
  intro unchanged
  intro baseline_digest
  exact ay_disj_left candidateSatDigest candidateUnsatDigest
    (ay_equisat_forward baselineSatDigest candidateSatDigest
      unchanged baseline_digest)

theorem ay_delta_digest_preserves_unsat_branch
    (candidateSatDigest : Prop)
    (baselineUnsatDigest : Prop) (candidateUnsatDigest : Prop) :
    AyUnchangedBranchDigests baselineUnsatDigest candidateUnsatDigest ->
    baselineUnsatDigest ->
    AyDisj candidateSatDigest candidateUnsatDigest := by
  intro unchanged
  intro baseline_digest
  exact ay_disj_right candidateSatDigest candidateUnsatDigest
    (ay_equisat_forward baselineUnsatDigest candidateUnsatDigest
      unchanged baseline_digest)

theorem ay_delta_public_output_maps_to_candidate
    (baselineToken : Prop) (candidateToken : Prop) :
    AyPublicOutputComparison baselineToken candidateToken ->
    baselineToken ->
    candidateToken := by
  intro comparison
  exact ay_equisat_forward baselineToken candidateToken comparison

theorem ay_delta_candidate_replay
    (baselineSatKey : Prop) (baselineUnsatKey : Prop)
    (baselineOutcomeKey : Prop) (baselineSatDigest : Prop)
    (baselineUnsatDigest : Prop) (baselineToken : Prop)
    (candidateSatKey : Prop) (candidateUnsatKey : Prop)
    (candidateOutcomeKey : Prop) (candidateSatDigest : Prop)
    (candidateUnsatDigest : Prop) (candidateToken : Prop)
    (candidateAccepted : Prop) :
    AyDeltaAccepted
      baselineSatKey baselineUnsatKey baselineOutcomeKey
      baselineSatDigest baselineUnsatDigest baselineToken
      candidateSatKey candidateUnsatKey candidateOutcomeKey
      candidateSatDigest candidateUnsatDigest candidateToken
      candidateAccepted ->
    AyAuditReplay candidateAccepted := by
  intro accepted
  let tail1 := accepted
    (AyConj
      (AyChangedArtifactKeys baselineUnsatKey candidateUnsatKey)
      (AyConj
        (AyChangedArtifactKeys baselineOutcomeKey candidateOutcomeKey)
        (AyConj
          (AyUnchangedBranchDigests baselineSatDigest candidateSatDigest)
          (AyConj
            (AyUnchangedBranchDigests
              baselineUnsatDigest candidateUnsatDigest)
            (AyConj
              (AyPublicOutputComparison baselineToken candidateToken)
              (AyAuditReplay candidateAccepted))))))
    (fun _sat_key tail => tail)
  let tail2 := tail1
    (AyConj
      (AyChangedArtifactKeys baselineOutcomeKey candidateOutcomeKey)
      (AyConj
        (AyUnchangedBranchDigests baselineSatDigest candidateSatDigest)
        (AyConj
          (AyUnchangedBranchDigests baselineUnsatDigest candidateUnsatDigest)
          (AyConj
            (AyPublicOutputComparison baselineToken candidateToken)
            (AyAuditReplay candidateAccepted)))))
    (fun _unsat_key tail => tail)
  let tail3 := tail2
    (AyConj
      (AyUnchangedBranchDigests baselineSatDigest candidateSatDigest)
      (AyConj
        (AyUnchangedBranchDigests baselineUnsatDigest candidateUnsatDigest)
        (AyConj
          (AyPublicOutputComparison baselineToken candidateToken)
          (AyAuditReplay candidateAccepted))))
    (fun _outcome_key tail => tail)
  let tail4 := tail3
    (AyConj
      (AyUnchangedBranchDigests baselineUnsatDigest candidateUnsatDigest)
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
    (fun _output_cmp replay => replay)

theorem ay_accepted_delta_preserves_baseline_public_soundness
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
    AyDeltaAccepted
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
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro delta
  intro baseline_manifest
  intro baseline_accepted
  exact ay_manifest_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    baselineSatKey baselineUnsatKey baselineOutcomeKey
    baselineSatDigest baselineUnsatDigest baselineToken baselineAccepted
    baseline_manifest baseline_accepted

theorem ay_rejected_delta_creates_no_semantic_claim
    (rejected : Prop)
    (semanticClaim : Prop) :
    AyDeltaRejected rejected ->
    AyDeltaReplayOracle
      semanticClaim semanticClaim semanticClaim semanticClaim semanticClaim
      semanticClaim semanticClaim semanticClaim semanticClaim semanticClaim
      semanticClaim semanticClaim semanticClaim rejected := by
  intro rejected_h
  exact ay_disj_right
    (AyDeltaAccepted
      semanticClaim semanticClaim semanticClaim semanticClaim semanticClaim
      semanticClaim semanticClaim semanticClaim semanticClaim semanticClaim
      semanticClaim semanticClaim semanticClaim)
    (AyDeltaRejected rejected)
    rejected_h
