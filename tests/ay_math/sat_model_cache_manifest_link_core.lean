-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for linking cached model checks to run
-- manifests. A public SAT report is justified exactly with matching manifest
-- witness identifiers and refined cache guards.

def AyMCMLConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMCMLDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMCMLEquisat (before : Prop) (after : Prop) :=
  AyMCMLConj (before -> after) (after -> before)

def AyMCMLManifestIds
    (run_manifest_id : Prop) (witness_manifest_id : Prop) :=
  AyMCMLConj run_manifest_id witness_manifest_id

def AyMCMLRefinedCacheGuard
    (coarse_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :=
  AyMCMLConj coarse_digest
    (AyMCMLConj witness_digest partition_digest)

def AyMCMLManifestGuardAgreement
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) :=
  AyMCMLConj manifest_ids
    (AyMCMLConj requested_guard stored_guard)

def AyMCMLAcceptedCacheReuse
    (requested_guard : Prop) (stored_guard : Prop) :=
  requested_guard -> stored_guard

def AyMCMLArtifactLookup
    (manifest_ids : Prop) (stored_guard : Prop) (artifact : Prop) :=
  manifest_ids -> stored_guard -> artifact

def AyMCMLVisibleProjection
    (artifact : Prop) (visible_model : Prop) :=
  artifact -> visible_model

def AyMCMLOriginalReconstruction
    (visible_model : Prop) (original_model : Prop) :=
  visible_model -> original_model

def AyMCMLPublicSatReport
    (manifest_ids : Prop) (stored_guard : Prop) (original_model : Prop) :=
  AyMCMLConj manifest_ids
    (AyMCMLConj stored_guard original_model)

def AyMCMLLinkedReport
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) (original_model : Prop) :=
  AyMCMLConj
    (AyMCMLManifestGuardAgreement
      manifest_ids requested_guard stored_guard)
    (AyMCMLPublicSatReport manifest_ids stored_guard original_model)

def AyMCMLNoPublicClaim (report : Prop) :=
  report -> False

theorem ay_mcml_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMCMLConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mcml_conj_left
    (left : Prop) (right : Prop) :
    AyMCMLConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mcml_conj_right
    (left : Prop) (right : Prop) :
    AyMCMLConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mcml_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMCMLDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mcml_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMCMLDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mcml_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMCMLEquisat before after := by
  intro forward
  intro backward
  exact ay_mcml_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_mcml_equisat_forward
    (before : Prop) (after : Prop) :
    AyMCMLEquisat before after -> before -> after := by
  intro certificate
  exact ay_mcml_conj_left (before -> after) (after -> before) certificate

theorem ay_mcml_equisat_backward
    (before : Prop) (after : Prop) :
    AyMCMLEquisat before after -> after -> before := by
  intro certificate
  exact ay_mcml_conj_right (before -> after) (after -> before) certificate

theorem ay_mcml_manifest_ids_intro
    (run_manifest_id : Prop) (witness_manifest_id : Prop) :
    run_manifest_id ->
    witness_manifest_id ->
    AyMCMLManifestIds run_manifest_id witness_manifest_id := by
  intro hrun
  intro hwitness
  exact ay_mcml_conj_intro run_manifest_id witness_manifest_id
    hrun hwitness

theorem ay_mcml_manifest_ids_run
    (run_manifest_id : Prop) (witness_manifest_id : Prop) :
    AyMCMLManifestIds run_manifest_id witness_manifest_id ->
    run_manifest_id := by
  intro ids
  exact ay_mcml_conj_left run_manifest_id witness_manifest_id ids

theorem ay_mcml_manifest_ids_witness
    (run_manifest_id : Prop) (witness_manifest_id : Prop) :
    AyMCMLManifestIds run_manifest_id witness_manifest_id ->
    witness_manifest_id := by
  intro ids
  exact ay_mcml_conj_right run_manifest_id witness_manifest_id ids

theorem ay_mcml_refined_guard_intro
    (coarse_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :
    coarse_digest ->
    witness_digest ->
    partition_digest ->
    AyMCMLRefinedCacheGuard
      coarse_digest witness_digest partition_digest := by
  intro hcoarse
  intro hwitness
  intro hpartition
  exact ay_mcml_conj_intro coarse_digest
    (AyMCMLConj witness_digest partition_digest)
    hcoarse
    (ay_mcml_conj_intro witness_digest partition_digest
      hwitness hpartition)

theorem ay_mcml_refined_guard_coarse
    (coarse_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :
    AyMCMLRefinedCacheGuard
      coarse_digest witness_digest partition_digest ->
    coarse_digest := by
  intro guard
  exact ay_mcml_conj_left coarse_digest
    (AyMCMLConj witness_digest partition_digest)
    guard

theorem ay_mcml_refined_guard_witness
    (coarse_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :
    AyMCMLRefinedCacheGuard
      coarse_digest witness_digest partition_digest ->
    witness_digest := by
  intro guard
  exact ay_mcml_conj_left witness_digest partition_digest
    (ay_mcml_conj_right coarse_digest
      (AyMCMLConj witness_digest partition_digest)
      guard)

theorem ay_mcml_refined_guard_partition
    (coarse_digest : Prop) (witness_digest : Prop)
    (partition_digest : Prop) :
    AyMCMLRefinedCacheGuard
      coarse_digest witness_digest partition_digest ->
    partition_digest := by
  intro guard
  exact ay_mcml_conj_right witness_digest partition_digest
    (ay_mcml_conj_right coarse_digest
      (AyMCMLConj witness_digest partition_digest)
      guard)

theorem ay_mcml_manifest_guard_agreement_intro
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) :
    manifest_ids ->
    requested_guard ->
    stored_guard ->
    AyMCMLManifestGuardAgreement
      manifest_ids requested_guard stored_guard := by
  intro hmanifest
  intro hrequested
  intro hstored
  exact ay_mcml_conj_intro manifest_ids
    (AyMCMLConj requested_guard stored_guard)
    hmanifest
    (ay_mcml_conj_intro requested_guard stored_guard
      hrequested hstored)

theorem ay_mcml_manifest_guard_agreement_manifest
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) :
    AyMCMLManifestGuardAgreement
      manifest_ids requested_guard stored_guard ->
    manifest_ids := by
  intro agreement
  exact ay_mcml_conj_left manifest_ids
    (AyMCMLConj requested_guard stored_guard)
    agreement

theorem ay_mcml_manifest_guard_agreement_requested
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) :
    AyMCMLManifestGuardAgreement
      manifest_ids requested_guard stored_guard ->
    requested_guard := by
  intro agreement
  exact ay_mcml_conj_left requested_guard stored_guard
    (ay_mcml_conj_right manifest_ids
      (AyMCMLConj requested_guard stored_guard)
      agreement)

theorem ay_mcml_manifest_guard_agreement_stored
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) :
    AyMCMLManifestGuardAgreement
      manifest_ids requested_guard stored_guard ->
    stored_guard := by
  intro agreement
  exact ay_mcml_conj_right requested_guard stored_guard
    (ay_mcml_conj_right manifest_ids
      (AyMCMLConj requested_guard stored_guard)
      agreement)

theorem ay_mcml_accept_reuse
    (requested_guard : Prop) (stored_guard : Prop) :
    AyMCMLAcceptedCacheReuse requested_guard stored_guard ->
    requested_guard ->
    stored_guard := by
  intro accepted
  intro hrequested
  exact accepted hrequested

theorem ay_mcml_agreement_from_manifest_and_reuse
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) :
    manifest_ids ->
    requested_guard ->
    AyMCMLAcceptedCacheReuse requested_guard stored_guard ->
    AyMCMLManifestGuardAgreement
      manifest_ids requested_guard stored_guard := by
  intro hmanifest
  intro hrequested
  intro accepted
  exact ay_mcml_manifest_guard_agreement_intro
    manifest_ids requested_guard stored_guard
    hmanifest hrequested (accepted hrequested)

theorem ay_mcml_artifact_lookup
    (manifest_ids : Prop) (stored_guard : Prop) (artifact : Prop) :
    AyMCMLArtifactLookup manifest_ids stored_guard artifact ->
    manifest_ids ->
    stored_guard ->
    artifact := by
  intro lookup
  intro hmanifest
  intro hstored
  exact lookup hmanifest hstored

theorem ay_mcml_lookup_after_reuse
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) (artifact : Prop) :
    AyMCMLAcceptedCacheReuse requested_guard stored_guard ->
    AyMCMLArtifactLookup manifest_ids stored_guard artifact ->
    manifest_ids ->
    requested_guard ->
    artifact := by
  intro accepted
  intro lookup
  intro hmanifest
  intro hrequested
  exact lookup hmanifest (accepted hrequested)

theorem ay_mcml_project_visible
    (artifact : Prop) (visible_model : Prop) :
    AyMCMLVisibleProjection artifact visible_model ->
    artifact ->
    visible_model := by
  intro project
  intro hartifact
  exact project hartifact

theorem ay_mcml_reconstruct_original
    (visible_model : Prop) (original_model : Prop) :
    AyMCMLOriginalReconstruction visible_model original_model ->
    visible_model ->
    original_model := by
  intro reconstruct
  intro hvisible
  exact reconstruct hvisible

theorem ay_mcml_original_from_manifest_cache
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) (artifact : Prop)
    (visible_model : Prop) (original_model : Prop) :
    AyMCMLAcceptedCacheReuse requested_guard stored_guard ->
    AyMCMLArtifactLookup manifest_ids stored_guard artifact ->
    AyMCMLVisibleProjection artifact visible_model ->
    AyMCMLOriginalReconstruction visible_model original_model ->
    manifest_ids ->
    requested_guard ->
    original_model := by
  intro accepted
  intro lookup
  intro project
  intro reconstruct
  intro hmanifest
  intro hrequested
  exact reconstruct (project (lookup hmanifest (accepted hrequested)))

theorem ay_mcml_public_report_intro
    (manifest_ids : Prop) (stored_guard : Prop)
    (original_model : Prop) :
    manifest_ids ->
    stored_guard ->
    original_model ->
    AyMCMLPublicSatReport
      manifest_ids stored_guard original_model := by
  intro hmanifest
  intro hstored
  intro horiginal
  exact ay_mcml_conj_intro manifest_ids
    (AyMCMLConj stored_guard original_model)
    hmanifest
    (ay_mcml_conj_intro stored_guard original_model
      hstored horiginal)

theorem ay_mcml_public_report_manifest
    (manifest_ids : Prop) (stored_guard : Prop)
    (original_model : Prop) :
    AyMCMLPublicSatReport manifest_ids stored_guard original_model ->
    manifest_ids := by
  intro report
  exact ay_mcml_conj_left manifest_ids
    (AyMCMLConj stored_guard original_model)
    report

theorem ay_mcml_public_report_guard
    (manifest_ids : Prop) (stored_guard : Prop)
    (original_model : Prop) :
    AyMCMLPublicSatReport manifest_ids stored_guard original_model ->
    stored_guard := by
  intro report
  exact ay_mcml_conj_left stored_guard original_model
    (ay_mcml_conj_right manifest_ids
      (AyMCMLConj stored_guard original_model)
      report)

theorem ay_mcml_public_report_original
    (manifest_ids : Prop) (stored_guard : Prop)
    (original_model : Prop) :
    AyMCMLPublicSatReport manifest_ids stored_guard original_model ->
    original_model := by
  intro report
  exact ay_mcml_conj_right stored_guard original_model
    (ay_mcml_conj_right manifest_ids
      (AyMCMLConj stored_guard original_model)
      report)

theorem ay_mcml_linked_report_intro
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) (original_model : Prop) :
    AyMCMLManifestGuardAgreement
      manifest_ids requested_guard stored_guard ->
    AyMCMLPublicSatReport manifest_ids stored_guard original_model ->
    AyMCMLLinkedReport
      manifest_ids requested_guard stored_guard original_model := by
  intro agreement
  intro report
  exact ay_mcml_conj_intro
    (AyMCMLManifestGuardAgreement
      manifest_ids requested_guard stored_guard)
    (AyMCMLPublicSatReport manifest_ids stored_guard original_model)
    agreement report

theorem ay_mcml_linked_report_agreement
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) (original_model : Prop) :
    AyMCMLLinkedReport
      manifest_ids requested_guard stored_guard original_model ->
    AyMCMLManifestGuardAgreement
      manifest_ids requested_guard stored_guard := by
  intro linked
  exact ay_mcml_conj_left
    (AyMCMLManifestGuardAgreement
      manifest_ids requested_guard stored_guard)
    (AyMCMLPublicSatReport manifest_ids stored_guard original_model)
    linked

theorem ay_mcml_linked_report_public
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) (original_model : Prop) :
    AyMCMLLinkedReport
      manifest_ids requested_guard stored_guard original_model ->
    AyMCMLPublicSatReport manifest_ids stored_guard original_model := by
  intro linked
  exact ay_mcml_conj_right
    (AyMCMLManifestGuardAgreement
      manifest_ids requested_guard stored_guard)
    (AyMCMLPublicSatReport manifest_ids stored_guard original_model)
    linked

theorem ay_mcml_manifest_linked_cache_report
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) (artifact : Prop)
    (visible_model : Prop) (original_model : Prop) :
    AyMCMLAcceptedCacheReuse requested_guard stored_guard ->
    AyMCMLArtifactLookup manifest_ids stored_guard artifact ->
    AyMCMLVisibleProjection artifact visible_model ->
    AyMCMLOriginalReconstruction visible_model original_model ->
    manifest_ids ->
    requested_guard ->
    AyMCMLLinkedReport
      manifest_ids requested_guard stored_guard original_model := by
  intro accepted
  intro lookup
  intro project
  intro reconstruct
  intro hmanifest
  intro hrequested
  let hstored := accepted hrequested
  let horiginal := reconstruct (project (lookup hmanifest hstored))
  exact ay_mcml_linked_report_intro
    manifest_ids requested_guard stored_guard original_model
    (ay_mcml_manifest_guard_agreement_intro
      manifest_ids requested_guard stored_guard
      hmanifest hrequested hstored)
    (ay_mcml_public_report_intro
      manifest_ids stored_guard original_model
      hmanifest hstored horiginal)

theorem ay_mcml_linked_report_sound
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) (original_model : Prop) :
    AyMCMLLinkedReport
      manifest_ids requested_guard stored_guard original_model ->
    original_model := by
  intro linked
  exact ay_mcml_public_report_original
    manifest_ids stored_guard original_model
    (ay_mcml_linked_report_public
      manifest_ids requested_guard stored_guard original_model linked)

theorem ay_mcml_manifest_link_sound_exact
    (manifest_ids : Prop) (requested_guard : Prop)
    (stored_guard : Prop) (original_model : Prop) :
    AyMCMLEquisat
      (AyMCMLLinkedReport
        manifest_ids requested_guard stored_guard original_model)
      (AyMCMLConj
        (AyMCMLManifestGuardAgreement
          manifest_ids requested_guard stored_guard)
        (AyMCMLPublicSatReport
          manifest_ids stored_guard original_model)) := by
  exact ay_mcml_equisat_intro
    (AyMCMLLinkedReport
      manifest_ids requested_guard stored_guard original_model)
    (AyMCMLConj
      (AyMCMLManifestGuardAgreement
        manifest_ids requested_guard stored_guard)
      (AyMCMLPublicSatReport
        manifest_ids stored_guard original_model))
    (fun linked =>
      ay_mcml_conj_intro
        (AyMCMLManifestGuardAgreement
          manifest_ids requested_guard stored_guard)
        (AyMCMLPublicSatReport
          manifest_ids stored_guard original_model)
        (ay_mcml_linked_report_agreement
          manifest_ids requested_guard stored_guard original_model linked)
        (ay_mcml_linked_report_public
          manifest_ids requested_guard stored_guard original_model linked))
    (fun both =>
      ay_mcml_linked_report_intro
        manifest_ids requested_guard stored_guard original_model
        (ay_mcml_conj_left
          (AyMCMLManifestGuardAgreement
            manifest_ids requested_guard stored_guard)
          (AyMCMLPublicSatReport
            manifest_ids stored_guard original_model)
          both)
        (ay_mcml_conj_right
          (AyMCMLManifestGuardAgreement
            manifest_ids requested_guard stored_guard)
          (AyMCMLPublicSatReport
            manifest_ids stored_guard original_model)
          both))

theorem ay_mcml_manifest_mismatch_no_report
    (manifest_ids : Prop) (report : Prop) :
    (manifest_ids -> False) ->
    (report -> manifest_ids) ->
    AyMCMLNoPublicClaim report := by
  intro mismatch
  intro report_to_manifest
  intro hreport
  exact mismatch (report_to_manifest hreport)

theorem ay_mcml_guard_mismatch_no_report
    (stored_guard : Prop) (report : Prop) :
    (stored_guard -> False) ->
    (report -> stored_guard) ->
    AyMCMLNoPublicClaim report := by
  intro mismatch
  intro report_to_guard
  intro hreport
  exact mismatch (report_to_guard hreport)

