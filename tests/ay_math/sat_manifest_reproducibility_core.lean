-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Reproducibility core for ay SAT-COMP run manifests. The file models the
-- public manifest fields and proves that matching digest/key/token evidence
-- lets a checker replay the same branch artifacts and public SAT/UNSAT theorem.

def AyDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyEquisat (before : Prop) (after : Prop) :=
  AyConj (before -> after) (after -> before)

def AyManifestVersion (version : Prop) :=
  version

def AyTraceDigest (digest : Prop) :=
  digest

def AyArchiveKeys (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop) :=
  AyConj satKey (AyConj unsatKey outcomeKey)

def AyBranchArtifactDigest (satDigest : Prop) (unsatDigest : Prop) :=
  AyDisj satDigest unsatDigest

def AyPublicOutputToken (satToken : Prop) (unsatToken : Prop) :=
  AyDisj satToken unsatToken

def AyAuditReplayDecision (accepted : Prop) :=
  accepted

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
    (version : Prop) (traceDigest : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop)
    (satDigest : Prop) (unsatDigest : Prop)
    (satToken : Prop) (unsatToken : Prop)
    (accepted : Prop) :=
  AyConj
    (AyManifestVersion version)
    (AyConj
      (AyTraceDigest traceDigest)
      (AyConj
        (AyArchiveKeys satKey unsatKey outcomeKey)
        (AyConj
          (AyBranchArtifactDigest satDigest unsatDigest)
          (AyConj
            (AyPublicOutputToken satToken unsatToken)
            (AyConj
              (AyAuditReplayDecision accepted)
              (accepted ->
                AyCompressedOutcome
                  originalFormula visibleFormula visibleModel originalModel
                  finalClause))))))

def AyMatchingManifestEvidence
    (versionA : Prop) (traceA : Prop)
    (satKeyA : Prop) (unsatKeyA : Prop) (outcomeKeyA : Prop)
    (satDigestA : Prop) (unsatDigestA : Prop)
    (satTokenA : Prop) (unsatTokenA : Prop) (acceptedA : Prop)
    (versionB : Prop) (traceB : Prop)
    (satKeyB : Prop) (unsatKeyB : Prop) (outcomeKeyB : Prop)
    (satDigestB : Prop) (unsatDigestB : Prop)
    (satTokenB : Prop) (unsatTokenB : Prop) (acceptedB : Prop) :=
  AyConj
    (AyEquisat versionA versionB)
    (AyConj
      (AyEquisat traceA traceB)
      (AyConj
        (AyEquisat satKeyA satKeyB)
        (AyConj
          (AyEquisat unsatKeyA unsatKeyB)
          (AyConj
            (AyEquisat outcomeKeyA outcomeKeyB)
            (AyConj
              (AyEquisat satDigestA satDigestB)
              (AyConj
                (AyEquisat unsatDigestA unsatDigestB)
                (AyConj
                  (AyEquisat satTokenA satTokenB)
                  (AyConj
                    (AyEquisat unsatTokenA unsatTokenB)
                    (AyEquisat acceptedA acceptedB)))))))))

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

theorem ay_sat_artifact_visible_model
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArtifact visibleModel originalModel ->
    visibleModel := by
  intro artifact
  exact ay_conj_left visibleModel
    (AyVisibleModelReconstruction visibleModel originalModel)
    artifact

theorem ay_sat_artifact_reconstruction
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArtifact visibleModel originalModel ->
    AyVisibleModelReconstruction visibleModel originalModel := by
  intro artifact
  exact artifact
    (AyVisibleModelReconstruction visibleModel originalModel)
    (fun _visible reconstruct => reconstruct)

theorem ay_sat_artifact_original_model
    (visibleModel : Prop) (originalModel : Prop) :
    AySatArtifact visibleModel originalModel ->
    originalModel := by
  intro artifact
  exact
    (ay_sat_artifact_reconstruction visibleModel originalModel artifact)
    (ay_sat_artifact_visible_model visibleModel originalModel artifact)

theorem ay_unsat_artifact_final_clause
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    finalClause := by
  intro artifact
  exact ay_conj_left finalClause
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    artifact

theorem ay_unsat_artifact_preprocessing
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    AyPreprocessingProof originalFormula visibleFormula := by
  intro artifact
  let proof_and_replay := artifact
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    (fun _final tail => tail)
  exact ay_conj_left
    (AyPreprocessingProof originalFormula visibleFormula)
    (AyUnsatReplayWitness visibleFormula finalClause)
    proof_and_replay

theorem ay_unsat_artifact_replay
    (originalFormula : Prop) (visibleFormula : Prop) (finalClause : Prop) :
    AyUnsatArtifact originalFormula visibleFormula finalClause ->
    AyUnsatReplayWitness visibleFormula finalClause := by
  intro artifact
  let proof_and_replay := artifact
    (AyConj
      (AyPreprocessingProof originalFormula visibleFormula)
      (AyUnsatReplayWitness visibleFormula finalClause))
    (fun _final tail => tail)
  exact proof_and_replay
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
    (ay_unsat_artifact_final_clause originalFormula visibleFormula finalClause
      artifact)
    ((ay_unsat_artifact_preprocessing
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
    (fun sat_artifact =>
      ay_disj_left originalModel (Not originalFormula)
        (ay_sat_artifact_original_model
          visibleModel originalModel sat_artifact))
    (fun unsat_artifact =>
      ay_disj_right originalModel (Not originalFormula)
        (ay_unsat_artifact_original_unsat
          originalFormula visibleFormula finalClause unsat_artifact))

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

theorem ay_manifest_version
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (version : Prop) (traceDigest : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop)
    (satDigest : Prop) (unsatDigest : Prop)
    (satToken : Prop) (unsatToken : Prop) (accepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      version traceDigest satKey unsatKey outcomeKey
      satDigest unsatDigest satToken unsatToken accepted ->
    AyManifestVersion version := by
  intro manifest
  exact ay_conj_left
    (AyManifestVersion version)
    (AyConj
      (AyTraceDigest traceDigest)
      (AyConj
        (AyArchiveKeys satKey unsatKey outcomeKey)
        (AyConj
          (AyBranchArtifactDigest satDigest unsatDigest)
          (AyConj
            (AyPublicOutputToken satToken unsatToken)
            (AyConj
              (AyAuditReplayDecision accepted)
              (accepted ->
                AyCompressedOutcome
                  originalFormula visibleFormula visibleModel originalModel
                  finalClause))))))
    manifest

theorem ay_manifest_trace
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (version : Prop) (traceDigest : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop)
    (satDigest : Prop) (unsatDigest : Prop)
    (satToken : Prop) (unsatToken : Prop) (accepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      version traceDigest satKey unsatKey outcomeKey
      satDigest unsatDigest satToken unsatToken accepted ->
    AyTraceDigest traceDigest := by
  intro manifest
  let tail := manifest
    (AyConj
      (AyTraceDigest traceDigest)
      (AyConj
        (AyArchiveKeys satKey unsatKey outcomeKey)
        (AyConj
          (AyBranchArtifactDigest satDigest unsatDigest)
          (AyConj
            (AyPublicOutputToken satToken unsatToken)
            (AyConj
              (AyAuditReplayDecision accepted)
              (accepted ->
                AyCompressedOutcome
                  originalFormula visibleFormula visibleModel originalModel
                  finalClause))))))
    (fun _version manifest_tail => manifest_tail)
  exact ay_conj_left
    (AyTraceDigest traceDigest)
    (AyConj
      (AyArchiveKeys satKey unsatKey outcomeKey)
      (AyConj
        (AyBranchArtifactDigest satDigest unsatDigest)
        (AyConj
          (AyPublicOutputToken satToken unsatToken)
          (AyConj
            (AyAuditReplayDecision accepted)
            (accepted ->
              AyCompressedOutcome
                originalFormula visibleFormula visibleModel originalModel
                finalClause)))))
    tail

theorem ay_manifest_keys
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (version : Prop) (traceDigest : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop)
    (satDigest : Prop) (unsatDigest : Prop)
    (satToken : Prop) (unsatToken : Prop) (accepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      version traceDigest satKey unsatKey outcomeKey
      satDigest unsatDigest satToken unsatToken accepted ->
    AyArchiveKeys satKey unsatKey outcomeKey := by
  intro manifest
  let tail1 := manifest
    (AyConj
      (AyTraceDigest traceDigest)
      (AyConj
        (AyArchiveKeys satKey unsatKey outcomeKey)
        (AyConj
          (AyBranchArtifactDigest satDigest unsatDigest)
          (AyConj
            (AyPublicOutputToken satToken unsatToken)
            (AyConj
              (AyAuditReplayDecision accepted)
              (accepted ->
                AyCompressedOutcome
                  originalFormula visibleFormula visibleModel originalModel
                  finalClause))))))
    (fun _version manifest_tail => manifest_tail)
  let tail2 := tail1
    (AyConj
      (AyArchiveKeys satKey unsatKey outcomeKey)
      (AyConj
        (AyBranchArtifactDigest satDigest unsatDigest)
        (AyConj
          (AyPublicOutputToken satToken unsatToken)
          (AyConj
            (AyAuditReplayDecision accepted)
            (accepted ->
              AyCompressedOutcome
                originalFormula visibleFormula visibleModel originalModel
                finalClause)))))
    (fun _trace manifest_tail => manifest_tail)
  exact ay_conj_left
    (AyArchiveKeys satKey unsatKey outcomeKey)
    (AyConj
      (AyBranchArtifactDigest satDigest unsatDigest)
      (AyConj
        (AyPublicOutputToken satToken unsatToken)
        (AyConj
          (AyAuditReplayDecision accepted)
          (accepted ->
            AyCompressedOutcome
              originalFormula visibleFormula visibleModel originalModel
              finalClause))))
    tail2

theorem ay_manifest_replay_outcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (version : Prop) (traceDigest : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop)
    (satDigest : Prop) (unsatDigest : Prop)
    (satToken : Prop) (unsatToken : Prop) (accepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      version traceDigest satKey unsatKey outcomeKey
      satDigest unsatDigest satToken unsatToken accepted ->
    accepted ->
    AyCompressedOutcome
      originalFormula visibleFormula visibleModel originalModel finalClause := by
  intro manifest
  let tail1 := manifest
    (AyConj
      (AyTraceDigest traceDigest)
      (AyConj
        (AyArchiveKeys satKey unsatKey outcomeKey)
        (AyConj
          (AyBranchArtifactDigest satDigest unsatDigest)
          (AyConj
            (AyPublicOutputToken satToken unsatToken)
            (AyConj
              (AyAuditReplayDecision accepted)
              (accepted ->
                AyCompressedOutcome
                  originalFormula visibleFormula visibleModel originalModel
                  finalClause))))))
    (fun _version manifest_tail => manifest_tail)
  let tail2 := tail1
    (AyConj
      (AyArchiveKeys satKey unsatKey outcomeKey)
      (AyConj
        (AyBranchArtifactDigest satDigest unsatDigest)
        (AyConj
          (AyPublicOutputToken satToken unsatToken)
          (AyConj
            (AyAuditReplayDecision accepted)
            (accepted ->
              AyCompressedOutcome
                originalFormula visibleFormula visibleModel originalModel
                finalClause)))))
    (fun _trace manifest_tail => manifest_tail)
  let tail3 := tail2
    (AyConj
      (AyBranchArtifactDigest satDigest unsatDigest)
      (AyConj
        (AyPublicOutputToken satToken unsatToken)
        (AyConj
          (AyAuditReplayDecision accepted)
          (accepted ->
            AyCompressedOutcome
              originalFormula visibleFormula visibleModel originalModel
              finalClause))))
    (fun _keys manifest_tail => manifest_tail)
  let tail4 := tail3
    (AyConj
      (AyPublicOutputToken satToken unsatToken)
      (AyConj
        (AyAuditReplayDecision accepted)
        (accepted ->
          AyCompressedOutcome
            originalFormula visibleFormula visibleModel originalModel
            finalClause)))
    (fun _digest manifest_tail => manifest_tail)
  let tail5 := tail4
    (AyConj
      (AyAuditReplayDecision accepted)
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
    (version : Prop) (traceDigest : Prop)
    (satKey : Prop) (unsatKey : Prop) (outcomeKey : Prop)
    (satDigest : Prop) (unsatDigest : Prop)
    (satToken : Prop) (unsatToken : Prop) (accepted : Prop) :
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      version traceDigest satKey unsatKey outcomeKey
      satDigest unsatDigest satToken unsatToken accepted ->
    accepted ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro manifest
  intro accepted_h
  exact ay_outcome_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    (ay_manifest_replay_outcome
      originalFormula visibleFormula visibleModel originalModel finalClause
      version traceDigest satKey unsatKey outcomeKey satDigest unsatDigest
      satToken unsatToken accepted manifest accepted_h)

theorem ay_matching_version_forward
    (versionA : Prop) (versionB : Prop) :
    AyEquisat versionA versionB ->
    AyManifestVersion versionA ->
    AyManifestVersion versionB := by
  intro matching
  exact ay_equisat_forward versionA versionB matching

theorem ay_matching_trace_forward
    (traceA : Prop) (traceB : Prop) :
    AyEquisat traceA traceB ->
    AyTraceDigest traceA ->
    AyTraceDigest traceB := by
  intro matching
  exact ay_equisat_forward traceA traceB matching

theorem ay_matching_sat_key_forward
    (satKeyA : Prop) (satKeyB : Prop) :
    AyEquisat satKeyA satKeyB ->
    satKeyA ->
    satKeyB := by
  intro matching
  exact ay_equisat_forward satKeyA satKeyB matching

theorem ay_matching_unsat_key_forward
    (unsatKeyA : Prop) (unsatKeyB : Prop) :
    AyEquisat unsatKeyA unsatKeyB ->
    unsatKeyA ->
    unsatKeyB := by
  intro matching
  exact ay_equisat_forward unsatKeyA unsatKeyB matching

theorem ay_matching_outcome_key_forward
    (outcomeKeyA : Prop) (outcomeKeyB : Prop) :
    AyEquisat outcomeKeyA outcomeKeyB ->
    outcomeKeyA ->
    outcomeKeyB := by
  intro matching
  exact ay_equisat_forward outcomeKeyA outcomeKeyB matching

theorem ay_matching_acceptance_forward
    (acceptedA : Prop) (acceptedB : Prop) :
    AyEquisat acceptedA acceptedB ->
    AyAuditReplayDecision acceptedA ->
    AyAuditReplayDecision acceptedB := by
  intro matching
  exact ay_equisat_forward acceptedA acceptedB matching

theorem ay_matching_sat_digest_replays
    (satDigestA : Prop) (unsatDigestA : Prop)
    (satDigestB : Prop) (unsatDigestB : Prop) :
    AyEquisat satDigestA satDigestB ->
    satDigestA ->
    AyBranchArtifactDigest satDigestB unsatDigestB := by
  intro matching
  intro digest_a
  exact ay_disj_left satDigestB unsatDigestB
    (ay_equisat_forward satDigestA satDigestB matching digest_a)

theorem ay_matching_unsat_digest_replays
    (satDigestB : Prop) (unsatDigestA : Prop) (unsatDigestB : Prop) :
    AyEquisat unsatDigestA unsatDigestB ->
    unsatDigestA ->
    AyBranchArtifactDigest satDigestB unsatDigestB := by
  intro matching
  intro digest_a
  exact ay_disj_right satDigestB unsatDigestB
    (ay_equisat_forward unsatDigestA unsatDigestB matching digest_a)

theorem ay_matching_sat_token_replays
    (satTokenA : Prop) (unsatTokenA : Prop)
    (satTokenB : Prop) (unsatTokenB : Prop) :
    AyEquisat satTokenA satTokenB ->
    satTokenA ->
    AyPublicOutputToken satTokenB unsatTokenB := by
  intro matching
  intro token_a
  exact ay_disj_left satTokenB unsatTokenB
    (ay_equisat_forward satTokenA satTokenB matching token_a)

theorem ay_matching_unsat_token_replays
    (satTokenB : Prop) (unsatTokenA : Prop) (unsatTokenB : Prop) :
    AyEquisat unsatTokenA unsatTokenB ->
    unsatTokenA ->
    AyPublicOutputToken satTokenB unsatTokenB := by
  intro matching
  intro token_a
  exact ay_disj_right satTokenB unsatTokenB
    (ay_equisat_forward unsatTokenA unsatTokenB matching token_a)

theorem ay_reproducible_sat_artifact_from_matching_key
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKeyA : Prop) (satKeyB : Prop)
    (unsatKeyB : Prop) (outcomeKeyB : Prop) :
    AyEquisat satKeyA satKeyB ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKeyB unsatKeyB outcomeKeyB ->
    satKeyA ->
    AySatArtifact visibleModel originalModel := by
  intro key_match
  intro archive_b
  intro sat_key_a
  exact ay_archive_sat_lookup
    originalFormula visibleFormula visibleModel originalModel finalClause
    satKeyB unsatKeyB outcomeKeyB
    archive_b
    (ay_matching_sat_key_forward satKeyA satKeyB key_match sat_key_a)

theorem ay_reproducible_unsat_artifact_from_matching_key
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKeyB : Prop) (unsatKeyA : Prop) (unsatKeyB : Prop)
    (outcomeKeyB : Prop) :
    AyEquisat unsatKeyA unsatKeyB ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKeyB unsatKeyB outcomeKeyB ->
    unsatKeyA ->
    AyUnsatArtifact originalFormula visibleFormula finalClause := by
  intro key_match
  intro archive_b
  intro unsat_key_a
  exact ay_archive_unsat_lookup
    originalFormula visibleFormula visibleModel originalModel finalClause
    satKeyB unsatKeyB outcomeKeyB
    archive_b
    (ay_matching_unsat_key_forward
      unsatKeyA unsatKeyB key_match unsat_key_a)

theorem ay_reproducible_public_soundness_from_matching_outcome
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKeyB : Prop) (unsatKeyB : Prop)
    (outcomeKeyA : Prop) (outcomeKeyB : Prop) :
    AyEquisat outcomeKeyA outcomeKeyB ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKeyB unsatKeyB outcomeKeyB ->
    outcomeKeyA ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro key_match
  intro archive_b
  intro outcome_key_a
  exact ay_outcome_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    (ay_archive_outcome_lookup
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKeyB unsatKeyB outcomeKeyB
      archive_b
      (ay_matching_outcome_key_forward
        outcomeKeyA outcomeKeyB key_match outcome_key_a))

theorem ay_reproducible_public_soundness_from_matching_replay
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (versionB : Prop) (traceB : Prop)
    (satKeyB : Prop) (unsatKeyB : Prop) (outcomeKeyB : Prop)
    (satDigestB : Prop) (unsatDigestB : Prop)
    (satTokenB : Prop) (unsatTokenB : Prop)
    (acceptedA : Prop) (acceptedB : Prop) :
    AyEquisat acceptedA acceptedB ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      versionB traceB satKeyB unsatKeyB outcomeKeyB
      satDigestB unsatDigestB satTokenB unsatTokenB acceptedB ->
    acceptedA ->
    AyPublicSoundnessTheorem originalFormula originalModel := by
  intro decision_match
  intro manifest_b
  intro accepted_a
  exact ay_manifest_public_soundness
    originalFormula visibleFormula visibleModel originalModel finalClause
    versionB traceB satKeyB unsatKeyB outcomeKeyB
    satDigestB unsatDigestB satTokenB unsatTokenB acceptedB
    manifest_b
    (ay_matching_acceptance_forward
      acceptedA acceptedB decision_match accepted_a)

theorem ay_two_matching_manifests_same_public_theorem
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (versionA : Prop) (traceA : Prop)
    (satKeyA : Prop) (unsatKeyA : Prop) (outcomeKeyA : Prop)
    (satDigestA : Prop) (unsatDigestA : Prop)
    (satTokenA : Prop) (unsatTokenA : Prop) (acceptedA : Prop)
    (versionB : Prop) (traceB : Prop)
    (satKeyB : Prop) (unsatKeyB : Prop) (outcomeKeyB : Prop)
    (satDigestB : Prop) (unsatDigestB : Prop)
    (satTokenB : Prop) (unsatTokenB : Prop) (acceptedB : Prop) :
    AyEquisat acceptedA acceptedB ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      versionA traceA satKeyA unsatKeyA outcomeKeyA
      satDigestA unsatDigestA satTokenA unsatTokenA acceptedA ->
    AyRunManifest
      originalFormula visibleFormula visibleModel originalModel finalClause
      versionB traceB satKeyB unsatKeyB outcomeKeyB
      satDigestB unsatDigestB satTokenB unsatTokenB acceptedB ->
    acceptedA ->
    AyConj
      (AyPublicSoundnessTheorem originalFormula originalModel)
      (AyPublicSoundnessTheorem originalFormula originalModel) := by
  intro decision_match
  intro manifest_a
  intro manifest_b
  intro accepted_a
  exact ay_conj_intro
    (AyPublicSoundnessTheorem originalFormula originalModel)
    (AyPublicSoundnessTheorem originalFormula originalModel)
    (ay_manifest_public_soundness
      originalFormula visibleFormula visibleModel originalModel finalClause
      versionA traceA satKeyA unsatKeyA outcomeKeyA
      satDigestA unsatDigestA satTokenA unsatTokenA acceptedA
      manifest_a accepted_a)
    (ay_reproducible_public_soundness_from_matching_replay
      originalFormula visibleFormula visibleModel originalModel finalClause
      versionB traceB satKeyB unsatKeyB outcomeKeyB
      satDigestB unsatDigestB satTokenB unsatTokenB
      acceptedA acceptedB decision_match manifest_b accepted_a)

theorem ay_two_matching_manifests_same_branch_artifacts
    (originalFormula : Prop) (visibleFormula : Prop)
    (visibleModel : Prop) (originalModel : Prop) (finalClause : Prop)
    (satKeyA : Prop) (satKeyB : Prop)
    (unsatKeyA : Prop) (unsatKeyB : Prop)
    (outcomeKeyB : Prop) :
    AyEquisat satKeyA satKeyB ->
    AyEquisat unsatKeyA unsatKeyB ->
    AyCertificateArchive
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKeyB unsatKeyB outcomeKeyB ->
    satKeyA ->
    unsatKeyA ->
    AyConj
      (AySatArtifact visibleModel originalModel)
      (AyUnsatArtifact originalFormula visibleFormula finalClause) := by
  intro sat_key_match
  intro unsat_key_match
  intro archive_b
  intro sat_key_a
  intro unsat_key_a
  exact ay_conj_intro
    (AySatArtifact visibleModel originalModel)
    (AyUnsatArtifact originalFormula visibleFormula finalClause)
    (ay_reproducible_sat_artifact_from_matching_key
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKeyA satKeyB unsatKeyB outcomeKeyB
      sat_key_match archive_b sat_key_a)
    (ay_reproducible_unsat_artifact_from_matching_key
      originalFormula visibleFormula visibleModel originalModel finalClause
      satKeyB unsatKeyA unsatKeyB outcomeKeyB
      unsat_key_match archive_b unsat_key_a)

