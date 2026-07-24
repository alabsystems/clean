-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for linking model-cache manifest reports to
-- validator SAT reports. The validator report is sound exactly when the
-- manifest-linked model-cache claim has matching identifiers and accepted
-- refined cache guards.

def AyMRLConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMRLDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMRLEquisat (before : Prop) (after : Prop) :=
  AyMRLConj (before -> after) (after -> before)

def AyMRLManifestWitnessIds
    (run_manifest_id : Prop) (cache_witness_id : Prop)
    (validator_witness_id : Prop) :=
  AyMRLConj run_manifest_id
    (AyMRLConj cache_witness_id validator_witness_id)

def AyMRLRefinedGuardAgreement
    (coarse_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :=
  AyMRLConj coarse_digest
    (AyMRLConj witness_digest partition_digest)

def AyMRLAcceptedModelCacheReuse
    (requested_guard : Prop) (stored_guard : Prop) :=
  requested_guard -> stored_guard

def AyMRLReportArtifactIds
    (cache_artifact_id : Prop) (validator_artifact_id : Prop) :=
  AyMRLConj cache_artifact_id validator_artifact_id

def AyMRLManifestLinkedCacheClaim
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (original_model : Prop) :=
  AyMRLConj manifest_ids
    (AyMRLConj artifact_ids
      (AyMRLConj requested_guard
        (AyMRLConj stored_guard original_model)))

def AyMRLArtifactLookup
    (manifest_ids : Prop) (artifact_ids : Prop)
    (stored_guard : Prop) (artifact : Prop) :=
  manifest_ids -> artifact_ids -> stored_guard -> artifact

def AyMRLVisibleProjection
    (artifact : Prop) (visible_model : Prop) :=
  artifact -> visible_model

def AyMRLOriginalReconstruction
    (visible_model : Prop) (original_model : Prop) :=
  visible_model -> original_model

def AyMRLValidatorSatReport
    (manifest_ids : Prop) (artifact_ids : Prop)
    (stored_guard : Prop) (original_model : Prop) :=
  AyMRLConj manifest_ids
    (AyMRLConj artifact_ids
      (AyMRLConj stored_guard original_model))

def AyMRLNoClaim (claim : Prop) :=
  claim -> False

theorem ay_mrl_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMRLConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mrl_conj_left
    (left : Prop) (right : Prop) :
    AyMRLConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mrl_conj_right
    (left : Prop) (right : Prop) :
    AyMRLConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mrl_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMRLDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mrl_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMRLDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mrl_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMRLEquisat before after := by
  intro forward
  intro backward
  exact ay_mrl_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_mrl_equisat_forward
    (before : Prop) (after : Prop) :
    AyMRLEquisat before after -> before -> after := by
  intro certificate
  exact ay_mrl_conj_left (before -> after) (after -> before) certificate

theorem ay_mrl_equisat_backward
    (before : Prop) (after : Prop) :
    AyMRLEquisat before after -> after -> before := by
  intro certificate
  exact ay_mrl_conj_right (before -> after) (after -> before) certificate

theorem ay_mrl_manifest_witness_ids_intro
    (run_manifest_id : Prop) (cache_witness_id : Prop)
    (validator_witness_id : Prop) :
    run_manifest_id ->
    cache_witness_id ->
    validator_witness_id ->
    AyMRLManifestWitnessIds
      run_manifest_id cache_witness_id validator_witness_id := by
  intro hrun
  intro hcache
  intro hvalidator
  exact ay_mrl_conj_intro run_manifest_id
    (AyMRLConj cache_witness_id validator_witness_id)
    hrun
    (ay_mrl_conj_intro cache_witness_id validator_witness_id
      hcache hvalidator)

theorem ay_mrl_manifest_witness_ids_run
    (run_manifest_id : Prop) (cache_witness_id : Prop)
    (validator_witness_id : Prop) :
    AyMRLManifestWitnessIds
      run_manifest_id cache_witness_id validator_witness_id ->
    run_manifest_id := by
  intro ids
  exact ay_mrl_conj_left run_manifest_id
    (AyMRLConj cache_witness_id validator_witness_id) ids

theorem ay_mrl_manifest_witness_ids_cache
    (run_manifest_id : Prop) (cache_witness_id : Prop)
    (validator_witness_id : Prop) :
    AyMRLManifestWitnessIds
      run_manifest_id cache_witness_id validator_witness_id ->
    cache_witness_id := by
  intro ids
  exact ay_mrl_conj_left cache_witness_id validator_witness_id
    (ay_mrl_conj_right run_manifest_id
      (AyMRLConj cache_witness_id validator_witness_id) ids)

theorem ay_mrl_manifest_witness_ids_validator
    (run_manifest_id : Prop) (cache_witness_id : Prop)
    (validator_witness_id : Prop) :
    AyMRLManifestWitnessIds
      run_manifest_id cache_witness_id validator_witness_id ->
    validator_witness_id := by
  intro ids
  exact ay_mrl_conj_right cache_witness_id validator_witness_id
    (ay_mrl_conj_right run_manifest_id
      (AyMRLConj cache_witness_id validator_witness_id) ids)

theorem ay_mrl_refined_guard_agreement_intro
    (coarse_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :
    coarse_digest ->
    witness_digest ->
    partition_digest ->
    AyMRLRefinedGuardAgreement
      coarse_digest witness_digest partition_digest := by
  intro hcoarse
  intro hwitness
  intro hpartition
  exact ay_mrl_conj_intro coarse_digest
    (AyMRLConj witness_digest partition_digest)
    hcoarse
    (ay_mrl_conj_intro witness_digest partition_digest
      hwitness hpartition)

theorem ay_mrl_refined_guard_coarse
    (coarse_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :
    AyMRLRefinedGuardAgreement
      coarse_digest witness_digest partition_digest ->
    coarse_digest := by
  intro guard
  exact ay_mrl_conj_left coarse_digest
    (AyMRLConj witness_digest partition_digest) guard

theorem ay_mrl_refined_guard_witness
    (coarse_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :
    AyMRLRefinedGuardAgreement
      coarse_digest witness_digest partition_digest ->
    witness_digest := by
  intro guard
  exact ay_mrl_conj_left witness_digest partition_digest
    (ay_mrl_conj_right coarse_digest
      (AyMRLConj witness_digest partition_digest) guard)

theorem ay_mrl_refined_guard_partition
    (coarse_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :
    AyMRLRefinedGuardAgreement
      coarse_digest witness_digest partition_digest ->
    partition_digest := by
  intro guard
  exact ay_mrl_conj_right witness_digest partition_digest
    (ay_mrl_conj_right coarse_digest
      (AyMRLConj witness_digest partition_digest) guard)

theorem ay_mrl_accept_model_cache_reuse
    (requested_guard : Prop) (stored_guard : Prop) :
    AyMRLAcceptedModelCacheReuse requested_guard stored_guard ->
    requested_guard ->
    stored_guard := by
  intro accepted
  intro hrequested
  exact accepted hrequested

theorem ay_mrl_report_artifact_ids_intro
    (cache_artifact_id : Prop) (validator_artifact_id : Prop) :
    cache_artifact_id ->
    validator_artifact_id ->
    AyMRLReportArtifactIds cache_artifact_id validator_artifact_id := by
  intro hcache
  intro hvalidator
  exact ay_mrl_conj_intro cache_artifact_id validator_artifact_id
    hcache hvalidator

theorem ay_mrl_report_artifact_ids_cache
    (cache_artifact_id : Prop) (validator_artifact_id : Prop) :
    AyMRLReportArtifactIds cache_artifact_id validator_artifact_id ->
    cache_artifact_id := by
  intro ids
  exact ay_mrl_conj_left cache_artifact_id validator_artifact_id ids

theorem ay_mrl_report_artifact_ids_validator
    (cache_artifact_id : Prop) (validator_artifact_id : Prop) :
    AyMRLReportArtifactIds cache_artifact_id validator_artifact_id ->
    validator_artifact_id := by
  intro ids
  exact ay_mrl_conj_right cache_artifact_id validator_artifact_id ids

theorem ay_mrl_artifact_lookup
    (manifest_ids : Prop) (artifact_ids : Prop)
    (stored_guard : Prop) (artifact : Prop) :
    AyMRLArtifactLookup manifest_ids artifact_ids stored_guard artifact ->
    manifest_ids ->
    artifact_ids ->
    stored_guard ->
    artifact := by
  intro lookup
  intro hmanifest
  intro hartifact_ids
  intro hstored
  exact lookup hmanifest hartifact_ids hstored

theorem ay_mrl_lookup_after_cache_reuse
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (artifact : Prop) :
    AyMRLAcceptedModelCacheReuse requested_guard stored_guard ->
    AyMRLArtifactLookup manifest_ids artifact_ids stored_guard artifact ->
    manifest_ids ->
    artifact_ids ->
    requested_guard ->
    artifact := by
  intro accepted
  intro lookup
  intro hmanifest
  intro hartifact_ids
  intro hrequested
  exact lookup hmanifest hartifact_ids (accepted hrequested)

theorem ay_mrl_project_visible
    (artifact : Prop) (visible_model : Prop) :
    AyMRLVisibleProjection artifact visible_model ->
    artifact ->
    visible_model := by
  intro project
  intro hartifact
  exact project hartifact

theorem ay_mrl_reconstruct_original
    (visible_model : Prop) (original_model : Prop) :
    AyMRLOriginalReconstruction visible_model original_model ->
    visible_model ->
    original_model := by
  intro reconstruct
  intro hvisible
  exact reconstruct hvisible

theorem ay_mrl_original_from_report_artifact
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (artifact : Prop) (visible_model : Prop)
    (original_model : Prop) :
    AyMRLAcceptedModelCacheReuse requested_guard stored_guard ->
    AyMRLArtifactLookup manifest_ids artifact_ids stored_guard artifact ->
    AyMRLVisibleProjection artifact visible_model ->
    AyMRLOriginalReconstruction visible_model original_model ->
    manifest_ids ->
    artifact_ids ->
    requested_guard ->
    original_model := by
  intro accepted
  intro lookup
  intro project
  intro reconstruct
  intro hmanifest
  intro hartifact_ids
  intro hrequested
  exact reconstruct
    (project (lookup hmanifest hartifact_ids (accepted hrequested)))

theorem ay_mrl_cache_claim_intro
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (original_model : Prop) :
    manifest_ids ->
    artifact_ids ->
    requested_guard ->
    stored_guard ->
    original_model ->
    AyMRLManifestLinkedCacheClaim
      manifest_ids artifact_ids requested_guard stored_guard original_model := by
  intro hmanifest
  intro hartifact_ids
  intro hrequested
  intro hstored
  intro horiginal
  exact ay_mrl_conj_intro manifest_ids
    (AyMRLConj artifact_ids
      (AyMRLConj requested_guard
        (AyMRLConj stored_guard original_model)))
    hmanifest
    (ay_mrl_conj_intro artifact_ids
      (AyMRLConj requested_guard
        (AyMRLConj stored_guard original_model))
      hartifact_ids
      (ay_mrl_conj_intro requested_guard
        (AyMRLConj stored_guard original_model)
        hrequested
        (ay_mrl_conj_intro stored_guard original_model
          hstored horiginal)))

theorem ay_mrl_cache_claim_manifest
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (original_model : Prop) :
    AyMRLManifestLinkedCacheClaim
      manifest_ids artifact_ids requested_guard stored_guard original_model ->
    manifest_ids := by
  intro claim
  exact ay_mrl_conj_left manifest_ids
    (AyMRLConj artifact_ids
      (AyMRLConj requested_guard
        (AyMRLConj stored_guard original_model))) claim

theorem ay_mrl_cache_claim_artifacts
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (original_model : Prop) :
    AyMRLManifestLinkedCacheClaim
      manifest_ids artifact_ids requested_guard stored_guard original_model ->
    artifact_ids := by
  intro claim
  exact ay_mrl_conj_left artifact_ids
    (AyMRLConj requested_guard
      (AyMRLConj stored_guard original_model))
    (ay_mrl_conj_right manifest_ids
      (AyMRLConj artifact_ids
        (AyMRLConj requested_guard
          (AyMRLConj stored_guard original_model))) claim)

theorem ay_mrl_cache_claim_requested
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (original_model : Prop) :
    AyMRLManifestLinkedCacheClaim
      manifest_ids artifact_ids requested_guard stored_guard original_model ->
    requested_guard := by
  intro claim
  exact ay_mrl_conj_left requested_guard
    (AyMRLConj stored_guard original_model)
    (ay_mrl_conj_right artifact_ids
      (AyMRLConj requested_guard
        (AyMRLConj stored_guard original_model))
      (ay_mrl_conj_right manifest_ids
        (AyMRLConj artifact_ids
          (AyMRLConj requested_guard
            (AyMRLConj stored_guard original_model))) claim))

theorem ay_mrl_cache_claim_stored
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (original_model : Prop) :
    AyMRLManifestLinkedCacheClaim
      manifest_ids artifact_ids requested_guard stored_guard original_model ->
    stored_guard := by
  intro claim
  exact ay_mrl_conj_left stored_guard original_model
    (ay_mrl_conj_right requested_guard
      (AyMRLConj stored_guard original_model)
      (ay_mrl_conj_right artifact_ids
        (AyMRLConj requested_guard
          (AyMRLConj stored_guard original_model))
        (ay_mrl_conj_right manifest_ids
          (AyMRLConj artifact_ids
            (AyMRLConj requested_guard
              (AyMRLConj stored_guard original_model))) claim)))

theorem ay_mrl_cache_claim_original
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (original_model : Prop) :
    AyMRLManifestLinkedCacheClaim
      manifest_ids artifact_ids requested_guard stored_guard original_model ->
    original_model := by
  intro claim
  exact ay_mrl_conj_right stored_guard original_model
    (ay_mrl_conj_right requested_guard
      (AyMRLConj stored_guard original_model)
      (ay_mrl_conj_right artifact_ids
        (AyMRLConj requested_guard
          (AyMRLConj stored_guard original_model))
        (ay_mrl_conj_right manifest_ids
          (AyMRLConj artifact_ids
            (AyMRLConj requested_guard
              (AyMRLConj stored_guard original_model))) claim)))

theorem ay_mrl_validator_report_intro
    (manifest_ids : Prop) (artifact_ids : Prop)
    (stored_guard : Prop) (original_model : Prop) :
    manifest_ids ->
    artifact_ids ->
    stored_guard ->
    original_model ->
    AyMRLValidatorSatReport
      manifest_ids artifact_ids stored_guard original_model := by
  intro hmanifest
  intro hartifact_ids
  intro hstored
  intro horiginal
  exact ay_mrl_conj_intro manifest_ids
    (AyMRLConj artifact_ids
      (AyMRLConj stored_guard original_model))
    hmanifest
    (ay_mrl_conj_intro artifact_ids
      (AyMRLConj stored_guard original_model)
      hartifact_ids
      (ay_mrl_conj_intro stored_guard original_model
        hstored horiginal))

theorem ay_mrl_validator_report_manifest
    (manifest_ids : Prop) (artifact_ids : Prop)
    (stored_guard : Prop) (original_model : Prop) :
    AyMRLValidatorSatReport
      manifest_ids artifact_ids stored_guard original_model ->
    manifest_ids := by
  intro report
  exact ay_mrl_conj_left manifest_ids
    (AyMRLConj artifact_ids
      (AyMRLConj stored_guard original_model)) report

theorem ay_mrl_validator_report_artifacts
    (manifest_ids : Prop) (artifact_ids : Prop)
    (stored_guard : Prop) (original_model : Prop) :
    AyMRLValidatorSatReport
      manifest_ids artifact_ids stored_guard original_model ->
    artifact_ids := by
  intro report
  exact ay_mrl_conj_left artifact_ids
    (AyMRLConj stored_guard original_model)
    (ay_mrl_conj_right manifest_ids
      (AyMRLConj artifact_ids
        (AyMRLConj stored_guard original_model)) report)

theorem ay_mrl_validator_report_guard
    (manifest_ids : Prop) (artifact_ids : Prop)
    (stored_guard : Prop) (original_model : Prop) :
    AyMRLValidatorSatReport
      manifest_ids artifact_ids stored_guard original_model ->
    stored_guard := by
  intro report
  exact ay_mrl_conj_left stored_guard original_model
    (ay_mrl_conj_right artifact_ids
      (AyMRLConj stored_guard original_model)
      (ay_mrl_conj_right manifest_ids
        (AyMRLConj artifact_ids
          (AyMRLConj stored_guard original_model)) report))

theorem ay_mrl_validator_report_original
    (manifest_ids : Prop) (artifact_ids : Prop)
    (stored_guard : Prop) (original_model : Prop) :
    AyMRLValidatorSatReport
      manifest_ids artifact_ids stored_guard original_model ->
    original_model := by
  intro report
  exact ay_mrl_conj_right stored_guard original_model
    (ay_mrl_conj_right artifact_ids
      (AyMRLConj stored_guard original_model)
      (ay_mrl_conj_right manifest_ids
        (AyMRLConj artifact_ids
          (AyMRLConj stored_guard original_model)) report))

theorem ay_mrl_cache_claim_to_validator_report
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (original_model : Prop) :
    AyMRLManifestLinkedCacheClaim
      manifest_ids artifact_ids requested_guard stored_guard original_model ->
    AyMRLValidatorSatReport
      manifest_ids artifact_ids stored_guard original_model := by
  intro claim
  exact ay_mrl_validator_report_intro
    manifest_ids artifact_ids stored_guard original_model
    (ay_mrl_cache_claim_manifest
      manifest_ids artifact_ids requested_guard stored_guard original_model
      claim)
    (ay_mrl_cache_claim_artifacts
      manifest_ids artifact_ids requested_guard stored_guard original_model
      claim)
    (ay_mrl_cache_claim_stored
      manifest_ids artifact_ids requested_guard stored_guard original_model
      claim)
    (ay_mrl_cache_claim_original
      manifest_ids artifact_ids requested_guard stored_guard original_model
      claim)

theorem ay_mrl_validator_report_to_cache_claim
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (original_model : Prop) :
    requested_guard ->
    AyMRLValidatorSatReport
      manifest_ids artifact_ids stored_guard original_model ->
    AyMRLManifestLinkedCacheClaim
      manifest_ids artifact_ids requested_guard stored_guard original_model := by
  intro hrequested
  intro report
  exact ay_mrl_cache_claim_intro
    manifest_ids artifact_ids requested_guard stored_guard original_model
    (ay_mrl_validator_report_manifest
      manifest_ids artifact_ids stored_guard original_model report)
    (ay_mrl_validator_report_artifacts
      manifest_ids artifact_ids stored_guard original_model report)
    hrequested
    (ay_mrl_validator_report_guard
      manifest_ids artifact_ids stored_guard original_model report)
    (ay_mrl_validator_report_original
      manifest_ids artifact_ids stored_guard original_model report)

theorem ay_mrl_validator_report_sound_exact
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (original_model : Prop) :
    requested_guard ->
    AyMRLEquisat
      (AyMRLManifestLinkedCacheClaim
        manifest_ids artifact_ids requested_guard stored_guard original_model)
      (AyMRLValidatorSatReport
        manifest_ids artifact_ids stored_guard original_model) := by
  intro hrequested
  exact ay_mrl_equisat_intro
    (AyMRLManifestLinkedCacheClaim
      manifest_ids artifact_ids requested_guard stored_guard original_model)
    (AyMRLValidatorSatReport
      manifest_ids artifact_ids stored_guard original_model)
    (ay_mrl_cache_claim_to_validator_report
      manifest_ids artifact_ids requested_guard stored_guard original_model)
    (ay_mrl_validator_report_to_cache_claim
      manifest_ids artifact_ids requested_guard stored_guard original_model
      hrequested)

theorem ay_mrl_accepted_cache_claim_from_artifact
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (artifact : Prop) (visible_model : Prop)
    (original_model : Prop) :
    AyMRLAcceptedModelCacheReuse requested_guard stored_guard ->
    AyMRLArtifactLookup manifest_ids artifact_ids stored_guard artifact ->
    AyMRLVisibleProjection artifact visible_model ->
    AyMRLOriginalReconstruction visible_model original_model ->
    manifest_ids ->
    artifact_ids ->
    requested_guard ->
    AyMRLManifestLinkedCacheClaim
      manifest_ids artifact_ids requested_guard stored_guard original_model := by
  intro accepted
  intro lookup
  intro project
  intro reconstruct
  intro hmanifest
  intro hartifact_ids
  intro hrequested
  exact ay_mrl_cache_claim_intro
    manifest_ids artifact_ids requested_guard stored_guard original_model
    hmanifest
    hartifact_ids
    hrequested
    (accepted hrequested)
    (ay_mrl_original_from_report_artifact
      manifest_ids artifact_ids requested_guard stored_guard artifact
      visible_model original_model
      accepted lookup project reconstruct hmanifest hartifact_ids hrequested)

theorem ay_mrl_validator_report_from_accepted_cache
    (manifest_ids : Prop) (artifact_ids : Prop)
    (requested_guard : Prop) (stored_guard : Prop)
    (artifact : Prop) (visible_model : Prop)
    (original_model : Prop) :
    AyMRLAcceptedModelCacheReuse requested_guard stored_guard ->
    AyMRLArtifactLookup manifest_ids artifact_ids stored_guard artifact ->
    AyMRLVisibleProjection artifact visible_model ->
    AyMRLOriginalReconstruction visible_model original_model ->
    manifest_ids ->
    artifact_ids ->
    requested_guard ->
    AyMRLValidatorSatReport
      manifest_ids artifact_ids stored_guard original_model := by
  intro accepted
  intro lookup
  intro project
  intro reconstruct
  intro hmanifest
  intro hartifact_ids
  intro hrequested
  exact ay_mrl_cache_claim_to_validator_report
    manifest_ids artifact_ids requested_guard stored_guard original_model
    (ay_mrl_accepted_cache_claim_from_artifact
      manifest_ids artifact_ids requested_guard stored_guard artifact
      visible_model original_model
      accepted lookup project reconstruct hmanifest hartifact_ids hrequested)

theorem ay_mrl_validator_report_sound_original
    (manifest_ids : Prop) (artifact_ids : Prop)
    (stored_guard : Prop) (original_model : Prop) :
    AyMRLValidatorSatReport
      manifest_ids artifact_ids stored_guard original_model ->
    original_model := by
  intro report
  exact ay_mrl_validator_report_original
    manifest_ids artifact_ids stored_guard original_model report

theorem ay_mrl_manifest_mismatch_no_claim
    (manifest_ids : Prop) (claim : Prop) :
    (manifest_ids -> False) ->
    (claim -> manifest_ids) ->
    AyMRLNoClaim claim := by
  intro mismatch
  intro claim_to_manifest
  intro hclaim
  exact mismatch (claim_to_manifest hclaim)

theorem ay_mrl_artifact_mismatch_no_claim
    (artifact_ids : Prop) (claim : Prop) :
    (artifact_ids -> False) ->
    (claim -> artifact_ids) ->
    AyMRLNoClaim claim := by
  intro mismatch
  intro claim_to_artifacts
  intro hclaim
  exact mismatch (claim_to_artifacts hclaim)

theorem ay_mrl_guard_mismatch_no_claim
    (stored_guard : Prop) (claim : Prop) :
    (stored_guard -> False) ->
    (claim -> stored_guard) ->
    AyMRLNoClaim claim := by
  intro mismatch
  intro claim_to_guard
  intro hclaim
  exact mismatch (claim_to_guard hclaim)

