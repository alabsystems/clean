-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton from model audit entries to Merkle-backed
-- public reports. A SAT answer is public only when model cache/report/audit
-- evidence is represented by an accepted leaf with membership and root
-- agreement; mismatch leaves are diagnostics with no public claim.

def AyMAMRConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMAMRDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMAMREquisat (before : Prop) (after : Prop) :=
  AyMAMRConj (before -> after) (after -> before)

def AyMAMRManifestLinkedReport
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (original_model : Prop) :=
  AyMAMRConj manifest_ids
    (AyMAMRConj artifact_ids
      (AyMAMRConj guard_agreement original_model))

def AyMAMRSatAuditEntry
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :=
  AyMAMRConj manifest_ids
    (AyMAMRConj artifact_ids
      (AyMAMRConj guard_agreement
        (AyMAMRConj digest_witness original_model)))

def AyMAMRLeafHash (entry : Prop) (leaf_hash : Prop) :=
  entry -> leaf_hash

def AyMAMRMerkleMembership
    (leaf_hash : Prop) (merkle_root : Prop) :=
  leaf_hash -> merkle_root

def AyMAMRReportRootAgreement
    (audit_root : Prop) (public_root : Prop) :=
  AyMAMRConj audit_root public_root

def AyMAMRAppendOnlyExtension
    (before_log : Prop) (entry : Prop) (after_log : Prop) :=
  before_log -> entry -> after_log

def AyMAMRMerkleBackedReport
    (entry : Prop) (leaf_hash : Prop)
    (merkle_root : Prop) (public_root : Prop) :=
  AyMAMRConj entry
    (AyMAMRConj leaf_hash
      (AyMAMRConj merkle_root public_root))

def AyMAMRDiagnosticMismatchLeaf
    (diagnostic : Prop) (leaf_hash : Prop) (public_claim : Prop) :=
  AyMAMRConj diagnostic
    (AyMAMRConj leaf_hash (public_claim -> False))

theorem ay_mamr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMAMRConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mamr_conj_left
    (left : Prop) (right : Prop) :
    AyMAMRConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mamr_conj_right
    (left : Prop) (right : Prop) :
    AyMAMRConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mamr_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMAMRDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mamr_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMAMRDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mamr_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMAMREquisat before after := by
  intro forward
  intro backward
  exact ay_mamr_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_mamr_equisat_forward
    (before : Prop) (after : Prop) :
    AyMAMREquisat before after -> before -> after := by
  intro certificate
  exact ay_mamr_conj_left (before -> after) (after -> before) certificate

theorem ay_mamr_equisat_backward
    (before : Prop) (after : Prop) :
    AyMAMREquisat before after -> after -> before := by
  intro certificate
  exact ay_mamr_conj_right (before -> after) (after -> before) certificate

theorem ay_mamr_manifest_report_intro
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (original_model : Prop) :
    manifest_ids ->
    artifact_ids ->
    guard_agreement ->
    original_model ->
    AyMAMRManifestLinkedReport
      manifest_ids artifact_ids guard_agreement original_model := by
  intro hmanifest
  intro hartifact
  intro hguard
  intro horiginal
  exact ay_mamr_conj_intro manifest_ids
    (AyMAMRConj artifact_ids
      (AyMAMRConj guard_agreement original_model))
    hmanifest
    (ay_mamr_conj_intro artifact_ids
      (AyMAMRConj guard_agreement original_model)
      hartifact
      (ay_mamr_conj_intro guard_agreement original_model
        hguard horiginal))

theorem ay_mamr_manifest_report_manifest
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (original_model : Prop) :
    AyMAMRManifestLinkedReport
      manifest_ids artifact_ids guard_agreement original_model ->
    manifest_ids := by
  intro report
  exact ay_mamr_conj_left manifest_ids
    (AyMAMRConj artifact_ids
      (AyMAMRConj guard_agreement original_model)) report

theorem ay_mamr_manifest_report_artifacts
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (original_model : Prop) :
    AyMAMRManifestLinkedReport
      manifest_ids artifact_ids guard_agreement original_model ->
    artifact_ids := by
  intro report
  exact ay_mamr_conj_left artifact_ids
    (AyMAMRConj guard_agreement original_model)
    (ay_mamr_conj_right manifest_ids
      (AyMAMRConj artifact_ids
        (AyMAMRConj guard_agreement original_model)) report)

theorem ay_mamr_manifest_report_guard
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (original_model : Prop) :
    AyMAMRManifestLinkedReport
      manifest_ids artifact_ids guard_agreement original_model ->
    guard_agreement := by
  intro report
  exact ay_mamr_conj_left guard_agreement original_model
    (ay_mamr_conj_right artifact_ids
      (AyMAMRConj guard_agreement original_model)
      (ay_mamr_conj_right manifest_ids
        (AyMAMRConj artifact_ids
          (AyMAMRConj guard_agreement original_model)) report))

theorem ay_mamr_manifest_report_original
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (original_model : Prop) :
    AyMAMRManifestLinkedReport
      manifest_ids artifact_ids guard_agreement original_model ->
    original_model := by
  intro report
  exact ay_mamr_conj_right guard_agreement original_model
    (ay_mamr_conj_right artifact_ids
      (AyMAMRConj guard_agreement original_model)
      (ay_mamr_conj_right manifest_ids
        (AyMAMRConj artifact_ids
          (AyMAMRConj guard_agreement original_model)) report))

theorem ay_mamr_sat_audit_entry_intro
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    manifest_ids ->
    artifact_ids ->
    guard_agreement ->
    digest_witness ->
    original_model ->
    AyMAMRSatAuditEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model := by
  intro hmanifest
  intro hartifact
  intro hguard
  intro hdigest
  intro horiginal
  exact ay_mamr_conj_intro manifest_ids
    (AyMAMRConj artifact_ids
      (AyMAMRConj guard_agreement
        (AyMAMRConj digest_witness original_model)))
    hmanifest
    (ay_mamr_conj_intro artifact_ids
      (AyMAMRConj guard_agreement
        (AyMAMRConj digest_witness original_model))
      hartifact
      (ay_mamr_conj_intro guard_agreement
        (AyMAMRConj digest_witness original_model)
        hguard
        (ay_mamr_conj_intro digest_witness original_model
          hdigest horiginal)))

theorem ay_mamr_sat_audit_entry_manifest
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMAMRSatAuditEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model ->
    manifest_ids := by
  intro entry
  exact ay_mamr_conj_left manifest_ids
    (AyMAMRConj artifact_ids
      (AyMAMRConj guard_agreement
        (AyMAMRConj digest_witness original_model))) entry

theorem ay_mamr_sat_audit_entry_artifacts
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMAMRSatAuditEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model ->
    artifact_ids := by
  intro entry
  exact ay_mamr_conj_left artifact_ids
    (AyMAMRConj guard_agreement
      (AyMAMRConj digest_witness original_model))
    (ay_mamr_conj_right manifest_ids
      (AyMAMRConj artifact_ids
        (AyMAMRConj guard_agreement
          (AyMAMRConj digest_witness original_model))) entry)

theorem ay_mamr_sat_audit_entry_guard
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMAMRSatAuditEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model ->
    guard_agreement := by
  intro entry
  exact ay_mamr_conj_left guard_agreement
    (AyMAMRConj digest_witness original_model)
    (ay_mamr_conj_right artifact_ids
      (AyMAMRConj guard_agreement
        (AyMAMRConj digest_witness original_model))
      (ay_mamr_conj_right manifest_ids
        (AyMAMRConj artifact_ids
          (AyMAMRConj guard_agreement
            (AyMAMRConj digest_witness original_model))) entry))

theorem ay_mamr_sat_audit_entry_digest
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMAMRSatAuditEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model ->
    digest_witness := by
  intro entry
  exact ay_mamr_conj_left digest_witness original_model
    (ay_mamr_conj_right guard_agreement
      (AyMAMRConj digest_witness original_model)
      (ay_mamr_conj_right artifact_ids
        (AyMAMRConj guard_agreement
          (AyMAMRConj digest_witness original_model))
        (ay_mamr_conj_right manifest_ids
          (AyMAMRConj artifact_ids
            (AyMAMRConj guard_agreement
              (AyMAMRConj digest_witness original_model))) entry)))

theorem ay_mamr_sat_audit_entry_original
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMAMRSatAuditEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model ->
    original_model := by
  intro entry
  exact ay_mamr_conj_right digest_witness original_model
    (ay_mamr_conj_right guard_agreement
      (AyMAMRConj digest_witness original_model)
      (ay_mamr_conj_right artifact_ids
        (AyMAMRConj guard_agreement
          (AyMAMRConj digest_witness original_model))
        (ay_mamr_conj_right manifest_ids
          (AyMAMRConj artifact_ids
            (AyMAMRConj guard_agreement
              (AyMAMRConj digest_witness original_model))) entry)))

theorem ay_mamr_sat_entry_from_manifest_report
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMAMRManifestLinkedReport
      manifest_ids artifact_ids guard_agreement original_model ->
    digest_witness ->
    AyMAMRSatAuditEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model := by
  intro report
  intro hdigest
  exact ay_mamr_sat_audit_entry_intro
    manifest_ids artifact_ids guard_agreement digest_witness original_model
    (ay_mamr_manifest_report_manifest
      manifest_ids artifact_ids guard_agreement original_model report)
    (ay_mamr_manifest_report_artifacts
      manifest_ids artifact_ids guard_agreement original_model report)
    (ay_mamr_manifest_report_guard
      manifest_ids artifact_ids guard_agreement original_model report)
    hdigest
    (ay_mamr_manifest_report_original
      manifest_ids artifact_ids guard_agreement original_model report)

theorem ay_mamr_manifest_report_from_sat_entry
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMAMRSatAuditEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model ->
    AyMAMRManifestLinkedReport
      manifest_ids artifact_ids guard_agreement original_model := by
  intro entry
  exact ay_mamr_manifest_report_intro
    manifest_ids artifact_ids guard_agreement original_model
    (ay_mamr_sat_audit_entry_manifest
      manifest_ids artifact_ids guard_agreement digest_witness
      original_model entry)
    (ay_mamr_sat_audit_entry_artifacts
      manifest_ids artifact_ids guard_agreement digest_witness
      original_model entry)
    (ay_mamr_sat_audit_entry_guard
      manifest_ids artifact_ids guard_agreement digest_witness
      original_model entry)
    (ay_mamr_sat_audit_entry_original
      manifest_ids artifact_ids guard_agreement digest_witness
      original_model entry)

theorem ay_mamr_leaf_hash_apply
    (entry : Prop) (leaf_hash : Prop) :
    AyMAMRLeafHash entry leaf_hash ->
    entry ->
    leaf_hash := by
  intro hash
  intro hentry
  exact hash hentry

theorem ay_mamr_merkle_membership_apply
    (leaf_hash : Prop) (merkle_root : Prop) :
    AyMAMRMerkleMembership leaf_hash merkle_root ->
    leaf_hash ->
    merkle_root := by
  intro membership
  intro hleaf
  exact membership hleaf

theorem ay_mamr_root_agreement_intro
    (audit_root : Prop) (public_root : Prop) :
    audit_root ->
    public_root ->
    AyMAMRReportRootAgreement audit_root public_root := by
  intro haudit
  intro hpublic
  exact ay_mamr_conj_intro audit_root public_root haudit hpublic

theorem ay_mamr_root_agreement_audit
    (audit_root : Prop) (public_root : Prop) :
    AyMAMRReportRootAgreement audit_root public_root ->
    audit_root := by
  intro agreement
  exact ay_mamr_conj_left audit_root public_root agreement

theorem ay_mamr_root_agreement_public
    (audit_root : Prop) (public_root : Prop) :
    AyMAMRReportRootAgreement audit_root public_root ->
    public_root := by
  intro agreement
  exact ay_mamr_conj_right audit_root public_root agreement

theorem ay_mamr_append_only_apply
    (before_log : Prop) (entry : Prop) (after_log : Prop) :
    AyMAMRAppendOnlyExtension before_log entry after_log ->
    before_log ->
    entry ->
    after_log := by
  intro append
  intro hbefore
  intro hentry
  exact append hbefore hentry

theorem ay_mamr_merkle_backed_report_intro
    (entry : Prop) (leaf_hash : Prop)
    (merkle_root : Prop) (public_root : Prop) :
    entry ->
    leaf_hash ->
    merkle_root ->
    public_root ->
    AyMAMRMerkleBackedReport
      entry leaf_hash merkle_root public_root := by
  intro hentry
  intro hleaf
  intro hroot
  intro hpublic
  exact ay_mamr_conj_intro entry
    (AyMAMRConj leaf_hash
      (AyMAMRConj merkle_root public_root))
    hentry
    (ay_mamr_conj_intro leaf_hash
      (AyMAMRConj merkle_root public_root)
      hleaf
      (ay_mamr_conj_intro merkle_root public_root hroot hpublic))

theorem ay_mamr_merkle_backed_report_entry
    (entry : Prop) (leaf_hash : Prop)
    (merkle_root : Prop) (public_root : Prop) :
    AyMAMRMerkleBackedReport
      entry leaf_hash merkle_root public_root ->
    entry := by
  intro backed
  exact ay_mamr_conj_left entry
    (AyMAMRConj leaf_hash
      (AyMAMRConj merkle_root public_root)) backed

theorem ay_mamr_merkle_backed_report_leaf
    (entry : Prop) (leaf_hash : Prop)
    (merkle_root : Prop) (public_root : Prop) :
    AyMAMRMerkleBackedReport
      entry leaf_hash merkle_root public_root ->
    leaf_hash := by
  intro backed
  exact ay_mamr_conj_left leaf_hash
    (AyMAMRConj merkle_root public_root)
    (ay_mamr_conj_right entry
      (AyMAMRConj leaf_hash
        (AyMAMRConj merkle_root public_root)) backed)

theorem ay_mamr_merkle_backed_report_root
    (entry : Prop) (leaf_hash : Prop)
    (merkle_root : Prop) (public_root : Prop) :
    AyMAMRMerkleBackedReport
      entry leaf_hash merkle_root public_root ->
    merkle_root := by
  intro backed
  exact ay_mamr_conj_left merkle_root public_root
    (ay_mamr_conj_right leaf_hash
      (AyMAMRConj merkle_root public_root)
      (ay_mamr_conj_right entry
        (AyMAMRConj leaf_hash
          (AyMAMRConj merkle_root public_root)) backed))

theorem ay_mamr_merkle_backed_report_public_root
    (entry : Prop) (leaf_hash : Prop)
    (merkle_root : Prop) (public_root : Prop) :
    AyMAMRMerkleBackedReport
      entry leaf_hash merkle_root public_root ->
    public_root := by
  intro backed
  exact ay_mamr_conj_right merkle_root public_root
    (ay_mamr_conj_right leaf_hash
      (AyMAMRConj merkle_root public_root)
      (ay_mamr_conj_right entry
        (AyMAMRConj leaf_hash
          (AyMAMRConj merkle_root public_root)) backed))

theorem ay_mamr_accepted_leaf_to_merkle_report
    (entry : Prop) (leaf_hash : Prop)
    (merkle_root : Prop) (public_root : Prop) :
    AyMAMRLeafHash entry leaf_hash ->
    AyMAMRMerkleMembership leaf_hash merkle_root ->
    AyMAMRReportRootAgreement merkle_root public_root ->
    entry ->
    AyMAMRMerkleBackedReport
      entry leaf_hash merkle_root public_root := by
  intro hash
  intro membership
  intro root_agreement
  intro hentry
  let hleaf := hash hentry
  let hroot := membership hleaf
  exact ay_mamr_merkle_backed_report_intro
    entry leaf_hash merkle_root public_root
    hentry
    hleaf
    hroot
    (ay_mamr_root_agreement_public
      merkle_root public_root root_agreement)

theorem ay_mamr_accepted_model_leaf_preserves_soundness
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) (leaf_hash : Prop)
    (merkle_root : Prop) (public_root : Prop) :
    AyMAMRLeafHash
      (AyMAMRSatAuditEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      leaf_hash ->
    AyMAMRMerkleMembership leaf_hash merkle_root ->
    AyMAMRReportRootAgreement merkle_root public_root ->
    AyMAMRSatAuditEntry manifest_ids artifact_ids
      guard_agreement digest_witness original_model ->
    original_model := by
  intro _hash
  intro _membership
  intro _root_agreement
  intro entry
  exact ay_mamr_sat_audit_entry_original
    manifest_ids artifact_ids guard_agreement digest_witness
    original_model entry

theorem ay_mamr_merkle_backed_model_report_sound
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) (leaf_hash : Prop)
    (merkle_root : Prop) (public_root : Prop) :
    AyMAMRMerkleBackedReport
      (AyMAMRSatAuditEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      leaf_hash merkle_root public_root ->
    original_model := by
  intro backed
  exact ay_mamr_sat_audit_entry_original
    manifest_ids artifact_ids guard_agreement digest_witness
    original_model
    (ay_mamr_merkle_backed_report_entry
      (AyMAMRSatAuditEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      leaf_hash merkle_root public_root backed)

theorem ay_mamr_append_then_merkle_report
    (before_log : Prop) (after_log : Prop)
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) (leaf_hash : Prop)
    (merkle_root : Prop) (public_root : Prop) :
    AyMAMRAppendOnlyExtension before_log
      (AyMAMRSatAuditEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      after_log ->
    AyMAMRLeafHash
      (AyMAMRSatAuditEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      leaf_hash ->
    AyMAMRMerkleMembership leaf_hash merkle_root ->
    AyMAMRReportRootAgreement merkle_root public_root ->
    before_log ->
    AyMAMRSatAuditEntry manifest_ids artifact_ids
      guard_agreement digest_witness original_model ->
    AyMAMRConj after_log
      (AyMAMRMerkleBackedReport
        (AyMAMRSatAuditEntry manifest_ids artifact_ids
          guard_agreement digest_witness original_model)
        leaf_hash merkle_root public_root) := by
  intro append
  intro hash
  intro membership
  intro root_agreement
  intro hbefore
  intro entry
  exact ay_mamr_conj_intro after_log
    (AyMAMRMerkleBackedReport
      (AyMAMRSatAuditEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      leaf_hash merkle_root public_root)
    (append hbefore entry)
    (ay_mamr_accepted_leaf_to_merkle_report
      (AyMAMRSatAuditEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      leaf_hash merkle_root public_root
      hash membership root_agreement entry)

theorem ay_mamr_manifest_report_equisat_audit_entry
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    digest_witness ->
    AyMAMREquisat
      (AyMAMRManifestLinkedReport
        manifest_ids artifact_ids guard_agreement original_model)
      (AyMAMRSatAuditEntry
        manifest_ids artifact_ids guard_agreement
        digest_witness original_model) := by
  intro hdigest
  exact ay_mamr_equisat_intro
    (AyMAMRManifestLinkedReport
      manifest_ids artifact_ids guard_agreement original_model)
    (AyMAMRSatAuditEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model)
    (fun report =>
      ay_mamr_sat_entry_from_manifest_report
        manifest_ids artifact_ids guard_agreement digest_witness
        original_model report hdigest)
    (ay_mamr_manifest_report_from_sat_entry
      manifest_ids artifact_ids guard_agreement digest_witness
      original_model)

theorem ay_mamr_diagnostic_leaf_intro
    (diagnostic : Prop) (leaf_hash : Prop) (public_claim : Prop) :
    diagnostic ->
    leaf_hash ->
    (public_claim -> False) ->
    AyMAMRDiagnosticMismatchLeaf
      diagnostic leaf_hash public_claim := by
  intro hdiagnostic
  intro hleaf
  intro blocks_claim
  exact ay_mamr_conj_intro diagnostic
    (AyMAMRConj leaf_hash (public_claim -> False))
    hdiagnostic
    (ay_mamr_conj_intro leaf_hash (public_claim -> False)
      hleaf blocks_claim)

theorem ay_mamr_diagnostic_leaf_diagnostic
    (diagnostic : Prop) (leaf_hash : Prop) (public_claim : Prop) :
    AyMAMRDiagnosticMismatchLeaf
      diagnostic leaf_hash public_claim ->
    diagnostic := by
  intro leaf
  exact ay_mamr_conj_left diagnostic
    (AyMAMRConj leaf_hash (public_claim -> False)) leaf

theorem ay_mamr_diagnostic_leaf_hash
    (diagnostic : Prop) (leaf_hash : Prop) (public_claim : Prop) :
    AyMAMRDiagnosticMismatchLeaf
      diagnostic leaf_hash public_claim ->
    leaf_hash := by
  intro leaf
  exact ay_mamr_conj_left leaf_hash (public_claim -> False)
    (ay_mamr_conj_right diagnostic
      (AyMAMRConj leaf_hash (public_claim -> False)) leaf)

theorem ay_mamr_diagnostic_leaf_blocks
    (diagnostic : Prop) (leaf_hash : Prop) (public_claim : Prop) :
    AyMAMRDiagnosticMismatchLeaf
      diagnostic leaf_hash public_claim ->
    public_claim ->
    False := by
  intro leaf
  exact ay_mamr_conj_right leaf_hash (public_claim -> False)
    (ay_mamr_conj_right diagnostic
      (AyMAMRConj leaf_hash (public_claim -> False)) leaf)

theorem ay_mamr_manifest_mismatch_leaf_no_claim
    (manifest_ids : Prop) (leaf_hash : Prop) (public_claim : Prop) :
    (manifest_ids -> False) ->
    leaf_hash ->
    (public_claim -> manifest_ids) ->
    AyMAMRDiagnosticMismatchLeaf
      (manifest_ids -> False) leaf_hash public_claim := by
  intro mismatch
  intro hleaf
  intro claim_to_manifest
  exact ay_mamr_diagnostic_leaf_intro
    (manifest_ids -> False) leaf_hash public_claim
    mismatch hleaf
    (fun claim => mismatch (claim_to_manifest claim))

theorem ay_mamr_artifact_mismatch_leaf_no_claim
    (artifact_ids : Prop) (leaf_hash : Prop) (public_claim : Prop) :
    (artifact_ids -> False) ->
    leaf_hash ->
    (public_claim -> artifact_ids) ->
    AyMAMRDiagnosticMismatchLeaf
      (artifact_ids -> False) leaf_hash public_claim := by
  intro mismatch
  intro hleaf
  intro claim_to_artifact
  exact ay_mamr_diagnostic_leaf_intro
    (artifact_ids -> False) leaf_hash public_claim
    mismatch hleaf
    (fun claim => mismatch (claim_to_artifact claim))

theorem ay_mamr_guard_mismatch_leaf_no_claim
    (guard_agreement : Prop) (leaf_hash : Prop) (public_claim : Prop) :
    (guard_agreement -> False) ->
    leaf_hash ->
    (public_claim -> guard_agreement) ->
    AyMAMRDiagnosticMismatchLeaf
      (guard_agreement -> False) leaf_hash public_claim := by
  intro mismatch
  intro hleaf
  intro claim_to_guard
  exact ay_mamr_diagnostic_leaf_intro
    (guard_agreement -> False) leaf_hash public_claim
    mismatch hleaf
    (fun claim => mismatch (claim_to_guard claim))

theorem ay_mamr_digest_mismatch_leaf_no_claim
    (digest_witness : Prop) (leaf_hash : Prop) (public_claim : Prop) :
    (digest_witness -> False) ->
    leaf_hash ->
    (public_claim -> digest_witness) ->
    AyMAMRDiagnosticMismatchLeaf
      (digest_witness -> False) leaf_hash public_claim := by
  intro mismatch
  intro hleaf
  intro claim_to_digest
  exact ay_mamr_diagnostic_leaf_intro
    (digest_witness -> False) leaf_hash public_claim
    mismatch hleaf
    (fun claim => mismatch (claim_to_digest claim))

theorem ay_mamr_diagnostic_mismatch_leaf_blocks_claim
    (diagnostic : Prop) (leaf_hash : Prop) (public_claim : Prop) :
    AyMAMRDiagnosticMismatchLeaf
      diagnostic leaf_hash public_claim ->
    public_claim ->
    False := by
  intro leaf
  intro claim
  exact ay_mamr_diagnostic_leaf_blocks
    diagnostic leaf_hash public_claim leaf claim

