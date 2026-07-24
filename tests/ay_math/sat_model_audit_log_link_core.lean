-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton linking model report proofs to append-only
-- validator audit logs. Accepted SAT report entries preserve the original
-- model claim after append; mismatch entries remain diagnostic no-claim facts.

def AyMALLConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMALLDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMALLEquisat (before : Prop) (after : Prop) :=
  AyMALLConj (before -> after) (after -> before)

def AyMALLManifestReport
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (original_model : Prop) :=
  AyMALLConj manifest_ids
    (AyMALLConj artifact_ids
      (AyMALLConj guard_agreement original_model))

def AyMALLSatReportEntry
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :=
  AyMALLConj manifest_ids
    (AyMALLConj artifact_ids
      (AyMALLConj guard_agreement
        (AyMALLConj digest_witness original_model)))

def AyMALLAuditLog (stable_prefix : Prop) (entries : Prop) :=
  AyMALLConj stable_prefix entries

def AyMALLAppendOnly
    (before_log : Prop) (entry : Prop) (after_log : Prop) :=
  before_log -> entry -> after_log

def AyMALLAuditDigestWitness
    (entry : Prop) (digest : Prop) :=
  entry -> digest

def AyMALLLoggedEntry
    (after_log : Prop) (entry : Prop) (digest : Prop) :=
  AyMALLConj after_log (AyMALLConj entry digest)

def AyMALLNoClaimEntry
    (diagnostic : Prop) (public_claim : Prop) :=
  AyMALLConj diagnostic (public_claim -> False)

theorem ay_mall_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMALLConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mall_conj_left
    (left : Prop) (right : Prop) :
    AyMALLConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mall_conj_right
    (left : Prop) (right : Prop) :
    AyMALLConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mall_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMALLDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mall_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMALLDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mall_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMALLEquisat before after := by
  intro forward
  intro backward
  exact ay_mall_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_mall_equisat_forward
    (before : Prop) (after : Prop) :
    AyMALLEquisat before after -> before -> after := by
  intro certificate
  exact ay_mall_conj_left (before -> after) (after -> before) certificate

theorem ay_mall_equisat_backward
    (before : Prop) (after : Prop) :
    AyMALLEquisat before after -> after -> before := by
  intro certificate
  exact ay_mall_conj_right (before -> after) (after -> before) certificate

theorem ay_mall_manifest_report_intro
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (original_model : Prop) :
    manifest_ids ->
    artifact_ids ->
    guard_agreement ->
    original_model ->
    AyMALLManifestReport
      manifest_ids artifact_ids guard_agreement original_model := by
  intro hmanifest
  intro hartifact
  intro hguard
  intro horiginal
  exact ay_mall_conj_intro manifest_ids
    (AyMALLConj artifact_ids
      (AyMALLConj guard_agreement original_model))
    hmanifest
    (ay_mall_conj_intro artifact_ids
      (AyMALLConj guard_agreement original_model)
      hartifact
      (ay_mall_conj_intro guard_agreement original_model
        hguard horiginal))

theorem ay_mall_manifest_report_manifest
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (original_model : Prop) :
    AyMALLManifestReport
      manifest_ids artifact_ids guard_agreement original_model ->
    manifest_ids := by
  intro report
  exact ay_mall_conj_left manifest_ids
    (AyMALLConj artifact_ids
      (AyMALLConj guard_agreement original_model)) report

theorem ay_mall_manifest_report_artifacts
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (original_model : Prop) :
    AyMALLManifestReport
      manifest_ids artifact_ids guard_agreement original_model ->
    artifact_ids := by
  intro report
  exact ay_mall_conj_left artifact_ids
    (AyMALLConj guard_agreement original_model)
    (ay_mall_conj_right manifest_ids
      (AyMALLConj artifact_ids
        (AyMALLConj guard_agreement original_model)) report)

theorem ay_mall_manifest_report_guard
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (original_model : Prop) :
    AyMALLManifestReport
      manifest_ids artifact_ids guard_agreement original_model ->
    guard_agreement := by
  intro report
  exact ay_mall_conj_left guard_agreement original_model
    (ay_mall_conj_right artifact_ids
      (AyMALLConj guard_agreement original_model)
      (ay_mall_conj_right manifest_ids
        (AyMALLConj artifact_ids
          (AyMALLConj guard_agreement original_model)) report))

theorem ay_mall_manifest_report_original
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (original_model : Prop) :
    AyMALLManifestReport
      manifest_ids artifact_ids guard_agreement original_model ->
    original_model := by
  intro report
  exact ay_mall_conj_right guard_agreement original_model
    (ay_mall_conj_right artifact_ids
      (AyMALLConj guard_agreement original_model)
      (ay_mall_conj_right manifest_ids
        (AyMALLConj artifact_ids
          (AyMALLConj guard_agreement original_model)) report))

theorem ay_mall_sat_entry_intro
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    manifest_ids ->
    artifact_ids ->
    guard_agreement ->
    digest_witness ->
    original_model ->
    AyMALLSatReportEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model := by
  intro hmanifest
  intro hartifact
  intro hguard
  intro hdigest
  intro horiginal
  exact ay_mall_conj_intro manifest_ids
    (AyMALLConj artifact_ids
      (AyMALLConj guard_agreement
        (AyMALLConj digest_witness original_model)))
    hmanifest
    (ay_mall_conj_intro artifact_ids
      (AyMALLConj guard_agreement
        (AyMALLConj digest_witness original_model))
      hartifact
      (ay_mall_conj_intro guard_agreement
        (AyMALLConj digest_witness original_model)
        hguard
        (ay_mall_conj_intro digest_witness original_model
          hdigest horiginal)))

theorem ay_mall_sat_entry_manifest
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMALLSatReportEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model ->
    manifest_ids := by
  intro entry
  exact ay_mall_conj_left manifest_ids
    (AyMALLConj artifact_ids
      (AyMALLConj guard_agreement
        (AyMALLConj digest_witness original_model))) entry

theorem ay_mall_sat_entry_artifacts
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMALLSatReportEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model ->
    artifact_ids := by
  intro entry
  exact ay_mall_conj_left artifact_ids
    (AyMALLConj guard_agreement
      (AyMALLConj digest_witness original_model))
    (ay_mall_conj_right manifest_ids
      (AyMALLConj artifact_ids
        (AyMALLConj guard_agreement
          (AyMALLConj digest_witness original_model))) entry)

theorem ay_mall_sat_entry_guard
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMALLSatReportEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model ->
    guard_agreement := by
  intro entry
  exact ay_mall_conj_left guard_agreement
    (AyMALLConj digest_witness original_model)
    (ay_mall_conj_right artifact_ids
      (AyMALLConj guard_agreement
        (AyMALLConj digest_witness original_model))
      (ay_mall_conj_right manifest_ids
        (AyMALLConj artifact_ids
          (AyMALLConj guard_agreement
            (AyMALLConj digest_witness original_model))) entry))

theorem ay_mall_sat_entry_digest
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMALLSatReportEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model ->
    digest_witness := by
  intro entry
  exact ay_mall_conj_left digest_witness original_model
    (ay_mall_conj_right guard_agreement
      (AyMALLConj digest_witness original_model)
      (ay_mall_conj_right artifact_ids
        (AyMALLConj guard_agreement
          (AyMALLConj digest_witness original_model))
        (ay_mall_conj_right manifest_ids
          (AyMALLConj artifact_ids
            (AyMALLConj guard_agreement
              (AyMALLConj digest_witness original_model))) entry)))

theorem ay_mall_sat_entry_original
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMALLSatReportEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model ->
    original_model := by
  intro entry
  exact ay_mall_conj_right digest_witness original_model
    (ay_mall_conj_right guard_agreement
      (AyMALLConj digest_witness original_model)
      (ay_mall_conj_right artifact_ids
        (AyMALLConj guard_agreement
          (AyMALLConj digest_witness original_model))
        (ay_mall_conj_right manifest_ids
          (AyMALLConj artifact_ids
            (AyMALLConj guard_agreement
              (AyMALLConj digest_witness original_model))) entry)))

theorem ay_mall_sat_entry_from_manifest_report
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMALLManifestReport
      manifest_ids artifact_ids guard_agreement original_model ->
    digest_witness ->
    AyMALLSatReportEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model := by
  intro report
  intro hdigest
  exact ay_mall_sat_entry_intro
    manifest_ids artifact_ids guard_agreement digest_witness original_model
    (ay_mall_manifest_report_manifest
      manifest_ids artifact_ids guard_agreement original_model report)
    (ay_mall_manifest_report_artifacts
      manifest_ids artifact_ids guard_agreement original_model report)
    (ay_mall_manifest_report_guard
      manifest_ids artifact_ids guard_agreement original_model report)
    hdigest
    (ay_mall_manifest_report_original
      manifest_ids artifact_ids guard_agreement original_model report)

theorem ay_mall_manifest_report_from_sat_entry
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    AyMALLSatReportEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model ->
    AyMALLManifestReport
      manifest_ids artifact_ids guard_agreement original_model := by
  intro entry
  exact ay_mall_manifest_report_intro
    manifest_ids artifact_ids guard_agreement original_model
    (ay_mall_sat_entry_manifest
      manifest_ids artifact_ids guard_agreement digest_witness
      original_model entry)
    (ay_mall_sat_entry_artifacts
      manifest_ids artifact_ids guard_agreement digest_witness
      original_model entry)
    (ay_mall_sat_entry_guard
      manifest_ids artifact_ids guard_agreement digest_witness
      original_model entry)
    (ay_mall_sat_entry_original
      manifest_ids artifact_ids guard_agreement digest_witness
      original_model entry)

theorem ay_mall_audit_log_intro
    (stable_prefix : Prop) (entries : Prop) :
    stable_prefix ->
    entries ->
    AyMALLAuditLog stable_prefix entries := by
  intro hprefix
  intro hentries
  exact ay_mall_conj_intro stable_prefix entries hprefix hentries

theorem ay_mall_audit_log_prefix
    (stable_prefix : Prop) (entries : Prop) :
    AyMALLAuditLog stable_prefix entries ->
    stable_prefix := by
  intro log
  exact ay_mall_conj_left stable_prefix entries log

theorem ay_mall_audit_log_entries
    (stable_prefix : Prop) (entries : Prop) :
    AyMALLAuditLog stable_prefix entries ->
    entries := by
  intro log
  exact ay_mall_conj_right stable_prefix entries log

theorem ay_mall_append_only_apply
    (before_log : Prop) (entry : Prop) (after_log : Prop) :
    AyMALLAppendOnly before_log entry after_log ->
    before_log ->
    entry ->
    after_log := by
  intro append
  intro hbefore
  intro hentry
  exact append hbefore hentry

theorem ay_mall_digest_witness_apply
    (entry : Prop) (digest : Prop) :
    AyMALLAuditDigestWitness entry digest ->
    entry ->
    digest := by
  intro witness
  intro hentry
  exact witness hentry

theorem ay_mall_logged_entry_intro
    (after_log : Prop) (entry : Prop) (digest : Prop) :
    after_log ->
    entry ->
    digest ->
    AyMALLLoggedEntry after_log entry digest := by
  intro hafter
  intro hentry
  intro hdigest
  exact ay_mall_conj_intro after_log
    (AyMALLConj entry digest)
    hafter
    (ay_mall_conj_intro entry digest hentry hdigest)

theorem ay_mall_logged_entry_log
    (after_log : Prop) (entry : Prop) (digest : Prop) :
    AyMALLLoggedEntry after_log entry digest ->
    after_log := by
  intro logged
  exact ay_mall_conj_left after_log (AyMALLConj entry digest) logged

theorem ay_mall_logged_entry_entry
    (after_log : Prop) (entry : Prop) (digest : Prop) :
    AyMALLLoggedEntry after_log entry digest ->
    entry := by
  intro logged
  exact ay_mall_conj_left entry digest
    (ay_mall_conj_right after_log (AyMALLConj entry digest) logged)

theorem ay_mall_logged_entry_digest
    (after_log : Prop) (entry : Prop) (digest : Prop) :
    AyMALLLoggedEntry after_log entry digest ->
    digest := by
  intro logged
  exact ay_mall_conj_right entry digest
    (ay_mall_conj_right after_log (AyMALLConj entry digest) logged)

theorem ay_mall_append_sat_entry_logged
    (before_log : Prop) (after_log : Prop)
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) (audit_digest : Prop) :
    AyMALLAppendOnly before_log
      (AyMALLSatReportEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      after_log ->
    AyMALLAuditDigestWitness
      (AyMALLSatReportEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      audit_digest ->
    before_log ->
    AyMALLSatReportEntry manifest_ids artifact_ids
      guard_agreement digest_witness original_model ->
    AyMALLLoggedEntry after_log
      (AyMALLSatReportEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      audit_digest := by
  intro append
  intro digest
  intro hbefore
  intro hentry
  exact ay_mall_logged_entry_intro after_log
    (AyMALLSatReportEntry manifest_ids artifact_ids
      guard_agreement digest_witness original_model)
    audit_digest
    (append hbefore hentry)
    hentry
    (digest hentry)

theorem ay_mall_appended_model_report_preserves_soundness
    (before_log : Prop) (after_log : Prop)
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) (audit_digest : Prop) :
    AyMALLAppendOnly before_log
      (AyMALLSatReportEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      after_log ->
    AyMALLAuditDigestWitness
      (AyMALLSatReportEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      audit_digest ->
    before_log ->
    AyMALLManifestReport
      manifest_ids artifact_ids guard_agreement original_model ->
    digest_witness ->
    original_model := by
  intro _append
  intro _digest
  intro _hbefore
  intro report
  intro _hdigest
  exact ay_mall_manifest_report_original
    manifest_ids artifact_ids guard_agreement original_model report

theorem ay_mall_logged_sat_entry_preserves_soundness
    (after_log : Prop) (manifest_ids : Prop)
    (artifact_ids : Prop) (guard_agreement : Prop)
    (digest_witness : Prop) (original_model : Prop)
    (audit_digest : Prop) :
    AyMALLLoggedEntry after_log
      (AyMALLSatReportEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      audit_digest ->
    original_model := by
  intro logged
  exact ay_mall_sat_entry_original
    manifest_ids artifact_ids guard_agreement digest_witness
    original_model
    (ay_mall_logged_entry_entry after_log
      (AyMALLSatReportEntry manifest_ids artifact_ids
        guard_agreement digest_witness original_model)
      audit_digest logged)

theorem ay_mall_logged_report_equisat_manifest
    (manifest_ids : Prop) (artifact_ids : Prop)
    (guard_agreement : Prop) (digest_witness : Prop)
    (original_model : Prop) :
    digest_witness ->
    AyMALLEquisat
      (AyMALLManifestReport
        manifest_ids artifact_ids guard_agreement original_model)
      (AyMALLSatReportEntry
        manifest_ids artifact_ids guard_agreement
        digest_witness original_model) := by
  intro hdigest
  exact ay_mall_equisat_intro
    (AyMALLManifestReport
      manifest_ids artifact_ids guard_agreement original_model)
    (AyMALLSatReportEntry
      manifest_ids artifact_ids guard_agreement
      digest_witness original_model)
    (fun report =>
      ay_mall_sat_entry_from_manifest_report
        manifest_ids artifact_ids guard_agreement digest_witness
        original_model report hdigest)
    (ay_mall_manifest_report_from_sat_entry
      manifest_ids artifact_ids guard_agreement digest_witness
      original_model)

theorem ay_mall_no_claim_entry_intro
    (diagnostic : Prop) (public_claim : Prop) :
    diagnostic ->
    (public_claim -> False) ->
    AyMALLNoClaimEntry diagnostic public_claim := by
  intro hdiagnostic
  intro blocks_claim
  exact ay_mall_conj_intro diagnostic
    (public_claim -> False) hdiagnostic blocks_claim

theorem ay_mall_no_claim_entry_diagnostic
    (diagnostic : Prop) (public_claim : Prop) :
    AyMALLNoClaimEntry diagnostic public_claim ->
    diagnostic := by
  intro entry
  exact ay_mall_conj_left diagnostic (public_claim -> False) entry

theorem ay_mall_no_claim_entry_blocks
    (diagnostic : Prop) (public_claim : Prop) :
    AyMALLNoClaimEntry diagnostic public_claim ->
    public_claim ->
    False := by
  intro entry
  exact ay_mall_conj_right diagnostic (public_claim -> False) entry

theorem ay_mall_manifest_mismatch_no_claim_entry
    (manifest_ids : Prop) (public_claim : Prop) :
    (manifest_ids -> False) ->
    (public_claim -> manifest_ids) ->
    manifest_ids -> False := by
  intro mismatch
  intro _claim_to_manifest
  intro hmanifest
  exact mismatch hmanifest

theorem ay_mall_manifest_mismatch_diagnostic
    (manifest_ids : Prop) (public_claim : Prop) :
    (manifest_ids -> False) ->
    (public_claim -> manifest_ids) ->
    AyMALLNoClaimEntry (manifest_ids -> False) public_claim := by
  intro mismatch
  intro claim_to_manifest
  exact ay_mall_no_claim_entry_intro
    (manifest_ids -> False) public_claim
    mismatch
    (fun claim => mismatch (claim_to_manifest claim))

theorem ay_mall_artifact_mismatch_diagnostic
    (artifact_ids : Prop) (public_claim : Prop) :
    (artifact_ids -> False) ->
    (public_claim -> artifact_ids) ->
    AyMALLNoClaimEntry (artifact_ids -> False) public_claim := by
  intro mismatch
  intro claim_to_artifact
  exact ay_mall_no_claim_entry_intro
    (artifact_ids -> False) public_claim
    mismatch
    (fun claim => mismatch (claim_to_artifact claim))

theorem ay_mall_guard_mismatch_diagnostic
    (guard_agreement : Prop) (public_claim : Prop) :
    (guard_agreement -> False) ->
    (public_claim -> guard_agreement) ->
    AyMALLNoClaimEntry (guard_agreement -> False) public_claim := by
  intro mismatch
  intro claim_to_guard
  exact ay_mall_no_claim_entry_intro
    (guard_agreement -> False) public_claim
    mismatch
    (fun claim => mismatch (claim_to_guard claim))

theorem ay_mall_digest_mismatch_diagnostic
    (audit_digest : Prop) (public_claim : Prop) :
    (audit_digest -> False) ->
    (public_claim -> audit_digest) ->
    AyMALLNoClaimEntry (audit_digest -> False) public_claim := by
  intro mismatch
  intro claim_to_digest
  exact ay_mall_no_claim_entry_intro
    (audit_digest -> False) public_claim
    mismatch
    (fun claim => mismatch (claim_to_digest claim))

theorem ay_mall_diagnostic_no_claim_blocks_report
    (diagnostic : Prop) (public_claim : Prop) :
    AyMALLNoClaimEntry diagnostic public_claim ->
    public_claim ->
    False := by
  intro entry
  intro claim
  exact ay_mall_no_claim_entry_blocks
    diagnostic public_claim entry claim

