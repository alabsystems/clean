-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for model delta transport across cache/report
-- boundaries. A transported delta model is public only when base assignment,
-- delta patch, reconstruction/projection, digest guard, and audit evidence
-- agree. Missing/corrupt deltas or base mismatches are no-claim diagnostics.

def AyMDTSConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMDTSDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMDTSEquisat (before : Prop) (after : Prop) :=
  AyMDTSConj (before -> after) (after -> before)

def AyMDTSBaseAssignment
    (base_assignment : Prop) (base_manifest : Prop) :=
  AyMDTSConj base_assignment base_manifest

def AyMDTSDeltaPatch
    (delta_patch : Prop) (delta_manifest : Prop) :=
  AyMDTSConj delta_patch delta_manifest

def AyMDTSTransportManifest
    (base_manifest : Prop) (delta_manifest : Prop)
    (target_manifest : Prop) :=
  AyMDTSConj base_manifest
    (AyMDTSConj delta_manifest target_manifest)

def AyMDTSDigestGuard
    (transport_manifest : Prop) (digest_guard : Prop) :=
  AyMDTSConj transport_manifest digest_guard

def AyMDTSDeltaReconstructionWitness
    (base_assignment : Prop) (delta_patch : Prop)
    (transported_assignment : Prop) :=
  base_assignment -> delta_patch -> transported_assignment

def AyMDTSProjectionWitness
    (transported_assignment : Prop) (original_model : Prop) :=
  transported_assignment -> original_model

def AyMDTSTransportEvidence
    (base_ok : Prop) (delta_ok : Prop)
    (projection_ok : Prop) (digest_guard : Prop) :=
  AyMDTSConj base_ok
    (AyMDTSConj delta_ok
      (AyMDTSConj projection_ok digest_guard))

def AyMDTSAuditEntry
    (transport_evidence : Prop) (audit_digest : Prop) :=
  AyMDTSConj transport_evidence audit_digest

def AyMDTSTransportedModelReport
    (transport_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :=
  AyMDTSConj transport_evidence
    (AyMDTSConj audit_entry original_model)

def AyMDTSNoClaimDiagnostic
    (diagnostic : Prop) (public_claim : Prop) :=
  AyMDTSConj diagnostic (public_claim -> False)

theorem ay_mdts_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMDTSConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mdts_conj_left
    (left : Prop) (right : Prop) :
    AyMDTSConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mdts_conj_right
    (left : Prop) (right : Prop) :
    AyMDTSConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mdts_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMDTSDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mdts_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMDTSDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mdts_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMDTSEquisat before after := by
  intro forward
  intro backward
  exact ay_mdts_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_mdts_equisat_forward
    (before : Prop) (after : Prop) :
    AyMDTSEquisat before after -> before -> after := by
  intro certificate
  exact ay_mdts_conj_left (before -> after) (after -> before) certificate

theorem ay_mdts_equisat_backward
    (before : Prop) (after : Prop) :
    AyMDTSEquisat before after -> after -> before := by
  intro certificate
  exact ay_mdts_conj_right (before -> after) (after -> before) certificate

theorem ay_mdts_base_assignment_intro
    (base_assignment : Prop) (base_manifest : Prop) :
    base_assignment ->
    base_manifest ->
    AyMDTSBaseAssignment base_assignment base_manifest := by
  intro hbase
  intro hmanifest
  exact ay_mdts_conj_intro base_assignment base_manifest
    hbase hmanifest

theorem ay_mdts_base_assignment_value
    (base_assignment : Prop) (base_manifest : Prop) :
    AyMDTSBaseAssignment base_assignment base_manifest ->
    base_assignment := by
  intro base
  exact ay_mdts_conj_left base_assignment base_manifest base

theorem ay_mdts_base_assignment_manifest
    (base_assignment : Prop) (base_manifest : Prop) :
    AyMDTSBaseAssignment base_assignment base_manifest ->
    base_manifest := by
  intro base
  exact ay_mdts_conj_right base_assignment base_manifest base

theorem ay_mdts_delta_patch_intro
    (delta_patch : Prop) (delta_manifest : Prop) :
    delta_patch ->
    delta_manifest ->
    AyMDTSDeltaPatch delta_patch delta_manifest := by
  intro hdelta
  intro hmanifest
  exact ay_mdts_conj_intro delta_patch delta_manifest
    hdelta hmanifest

theorem ay_mdts_delta_patch_value
    (delta_patch : Prop) (delta_manifest : Prop) :
    AyMDTSDeltaPatch delta_patch delta_manifest ->
    delta_patch := by
  intro hdelta
  exact ay_mdts_conj_left delta_patch delta_manifest hdelta

theorem ay_mdts_delta_patch_manifest
    (delta_patch : Prop) (delta_manifest : Prop) :
    AyMDTSDeltaPatch delta_patch delta_manifest ->
    delta_manifest := by
  intro hdelta
  exact ay_mdts_conj_right delta_patch delta_manifest hdelta

theorem ay_mdts_transport_manifest_intro
    (base_manifest : Prop) (delta_manifest : Prop)
    (target_manifest : Prop) :
    base_manifest ->
    delta_manifest ->
    target_manifest ->
    AyMDTSTransportManifest
      base_manifest delta_manifest target_manifest := by
  intro hbase
  intro hdelta
  intro htarget
  exact ay_mdts_conj_intro base_manifest
    (AyMDTSConj delta_manifest target_manifest)
    hbase
    (ay_mdts_conj_intro delta_manifest target_manifest
      hdelta htarget)

theorem ay_mdts_transport_manifest_base
    (base_manifest : Prop) (delta_manifest : Prop)
    (target_manifest : Prop) :
    AyMDTSTransportManifest
      base_manifest delta_manifest target_manifest ->
    base_manifest := by
  intro manifest
  exact ay_mdts_conj_left base_manifest
    (AyMDTSConj delta_manifest target_manifest) manifest

theorem ay_mdts_transport_manifest_delta
    (base_manifest : Prop) (delta_manifest : Prop)
    (target_manifest : Prop) :
    AyMDTSTransportManifest
      base_manifest delta_manifest target_manifest ->
    delta_manifest := by
  intro manifest
  exact ay_mdts_conj_left delta_manifest target_manifest
    (ay_mdts_conj_right base_manifest
      (AyMDTSConj delta_manifest target_manifest) manifest)

theorem ay_mdts_transport_manifest_target
    (base_manifest : Prop) (delta_manifest : Prop)
    (target_manifest : Prop) :
    AyMDTSTransportManifest
      base_manifest delta_manifest target_manifest ->
    target_manifest := by
  intro manifest
  exact ay_mdts_conj_right delta_manifest target_manifest
    (ay_mdts_conj_right base_manifest
      (AyMDTSConj delta_manifest target_manifest) manifest)

theorem ay_mdts_digest_guard_intro
    (transport_manifest : Prop) (digest_guard : Prop) :
    transport_manifest ->
    digest_guard ->
    AyMDTSDigestGuard transport_manifest digest_guard := by
  intro hmanifest
  intro hdigest
  exact ay_mdts_conj_intro transport_manifest digest_guard
    hmanifest hdigest

theorem ay_mdts_digest_guard_manifest
    (transport_manifest : Prop) (digest_guard : Prop) :
    AyMDTSDigestGuard transport_manifest digest_guard ->
    transport_manifest := by
  intro guard
  exact ay_mdts_conj_left transport_manifest digest_guard guard

theorem ay_mdts_digest_guard_digest
    (transport_manifest : Prop) (digest_guard : Prop) :
    AyMDTSDigestGuard transport_manifest digest_guard ->
    digest_guard := by
  intro guard
  exact ay_mdts_conj_right transport_manifest digest_guard guard

theorem ay_mdts_delta_reconstruct_apply
    (base_assignment : Prop) (delta_patch : Prop)
    (transported_assignment : Prop) :
    AyMDTSDeltaReconstructionWitness
      base_assignment delta_patch transported_assignment ->
    base_assignment ->
    delta_patch ->
    transported_assignment := by
  intro reconstruct
  intro hbase
  intro hdelta
  exact reconstruct hbase hdelta

theorem ay_mdts_projection_apply
    (transported_assignment : Prop) (original_model : Prop) :
    AyMDTSProjectionWitness transported_assignment original_model ->
    transported_assignment ->
    original_model := by
  intro project
  intro htransported
  exact project htransported

theorem ay_mdts_transport_evidence_intro
    (base_ok : Prop) (delta_ok : Prop)
    (projection_ok : Prop) (digest_guard : Prop) :
    base_ok ->
    delta_ok ->
    projection_ok ->
    digest_guard ->
    AyMDTSTransportEvidence
      base_ok delta_ok projection_ok digest_guard := by
  intro hbase
  intro hdelta
  intro hprojection
  intro hdigest
  exact ay_mdts_conj_intro base_ok
    (AyMDTSConj delta_ok
      (AyMDTSConj projection_ok digest_guard))
    hbase
    (ay_mdts_conj_intro delta_ok
      (AyMDTSConj projection_ok digest_guard)
      hdelta
      (ay_mdts_conj_intro projection_ok digest_guard
        hprojection hdigest))

theorem ay_mdts_transport_evidence_base
    (base_ok : Prop) (delta_ok : Prop)
    (projection_ok : Prop) (digest_guard : Prop) :
    AyMDTSTransportEvidence
      base_ok delta_ok projection_ok digest_guard ->
    base_ok := by
  intro evidence
  exact ay_mdts_conj_left base_ok
    (AyMDTSConj delta_ok
      (AyMDTSConj projection_ok digest_guard)) evidence

theorem ay_mdts_transport_evidence_delta
    (base_ok : Prop) (delta_ok : Prop)
    (projection_ok : Prop) (digest_guard : Prop) :
    AyMDTSTransportEvidence
      base_ok delta_ok projection_ok digest_guard ->
    delta_ok := by
  intro evidence
  exact ay_mdts_conj_left delta_ok
    (AyMDTSConj projection_ok digest_guard)
    (ay_mdts_conj_right base_ok
      (AyMDTSConj delta_ok
        (AyMDTSConj projection_ok digest_guard)) evidence)

theorem ay_mdts_transport_evidence_projection
    (base_ok : Prop) (delta_ok : Prop)
    (projection_ok : Prop) (digest_guard : Prop) :
    AyMDTSTransportEvidence
      base_ok delta_ok projection_ok digest_guard ->
    projection_ok := by
  intro evidence
  exact ay_mdts_conj_left projection_ok digest_guard
    (ay_mdts_conj_right delta_ok
      (AyMDTSConj projection_ok digest_guard)
      (ay_mdts_conj_right base_ok
        (AyMDTSConj delta_ok
          (AyMDTSConj projection_ok digest_guard)) evidence))

theorem ay_mdts_transport_evidence_digest
    (base_ok : Prop) (delta_ok : Prop)
    (projection_ok : Prop) (digest_guard : Prop) :
    AyMDTSTransportEvidence
      base_ok delta_ok projection_ok digest_guard ->
    digest_guard := by
  intro evidence
  exact ay_mdts_conj_right projection_ok digest_guard
    (ay_mdts_conj_right delta_ok
      (AyMDTSConj projection_ok digest_guard)
      (ay_mdts_conj_right base_ok
        (AyMDTSConj delta_ok
          (AyMDTSConj projection_ok digest_guard)) evidence))

theorem ay_mdts_audit_entry_intro
    (transport_evidence : Prop) (audit_digest : Prop) :
    transport_evidence ->
    audit_digest ->
    AyMDTSAuditEntry transport_evidence audit_digest := by
  intro hevidence
  intro haudit
  exact ay_mdts_conj_intro transport_evidence audit_digest
    hevidence haudit

theorem ay_mdts_audit_entry_evidence
    (transport_evidence : Prop) (audit_digest : Prop) :
    AyMDTSAuditEntry transport_evidence audit_digest ->
    transport_evidence := by
  intro audit
  exact ay_mdts_conj_left transport_evidence audit_digest audit

theorem ay_mdts_audit_entry_digest
    (transport_evidence : Prop) (audit_digest : Prop) :
    AyMDTSAuditEntry transport_evidence audit_digest ->
    audit_digest := by
  intro audit
  exact ay_mdts_conj_right transport_evidence audit_digest audit

theorem ay_mdts_report_intro
    (transport_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    transport_evidence ->
    audit_entry ->
    original_model ->
    AyMDTSTransportedModelReport
      transport_evidence audit_entry original_model := by
  intro hevidence
  intro haudit
  intro horiginal
  exact ay_mdts_conj_intro transport_evidence
    (AyMDTSConj audit_entry original_model)
    hevidence
    (ay_mdts_conj_intro audit_entry original_model
      haudit horiginal)

theorem ay_mdts_report_evidence
    (transport_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMDTSTransportedModelReport
      transport_evidence audit_entry original_model ->
    transport_evidence := by
  intro report
  exact ay_mdts_conj_left transport_evidence
    (AyMDTSConj audit_entry original_model) report

theorem ay_mdts_report_audit
    (transport_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMDTSTransportedModelReport
      transport_evidence audit_entry original_model ->
    audit_entry := by
  intro report
  exact ay_mdts_conj_left audit_entry original_model
    (ay_mdts_conj_right transport_evidence
      (AyMDTSConj audit_entry original_model) report)

theorem ay_mdts_report_original
    (transport_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMDTSTransportedModelReport
      transport_evidence audit_entry original_model ->
    original_model := by
  intro report
  exact ay_mdts_conj_right audit_entry original_model
    (ay_mdts_conj_right transport_evidence
      (AyMDTSConj audit_entry original_model) report)

theorem ay_mdts_transport_original_model
    (base_assignment : Prop) (delta_patch : Prop)
    (transported_assignment : Prop) (original_model : Prop) :
    AyMDTSDeltaReconstructionWitness
      base_assignment delta_patch transported_assignment ->
    AyMDTSProjectionWitness transported_assignment original_model ->
    base_assignment ->
    delta_patch ->
    original_model := by
  intro reconstruct
  intro project
  intro hbase
  intro hdelta
  exact project (reconstruct hbase hdelta)

theorem ay_mdts_transport_report_from_evidence
    (base_assignment : Prop) (delta_patch : Prop)
    (transported_assignment : Prop) (original_model : Prop)
    (base_ok : Prop) (delta_ok : Prop)
    (projection_ok : Prop) (digest_guard : Prop)
    (audit_entry : Prop) :
    AyMDTSDeltaReconstructionWitness
      base_assignment delta_patch transported_assignment ->
    AyMDTSProjectionWitness transported_assignment original_model ->
    base_assignment ->
    delta_patch ->
    base_ok ->
    delta_ok ->
    projection_ok ->
    digest_guard ->
    audit_entry ->
    AyMDTSTransportedModelReport
      (AyMDTSTransportEvidence
        base_ok delta_ok projection_ok digest_guard)
      audit_entry original_model := by
  intro reconstruct
  intro project
  intro hbase
  intro hdelta
  intro hbase_ok
  intro hdelta_ok
  intro hprojection
  intro hdigest
  intro haudit
  exact ay_mdts_report_intro
    (AyMDTSTransportEvidence
      base_ok delta_ok projection_ok digest_guard)
    audit_entry original_model
    (ay_mdts_transport_evidence_intro
      base_ok delta_ok projection_ok digest_guard
      hbase_ok hdelta_ok hprojection hdigest)
    haudit
    (project (reconstruct hbase hdelta))

theorem ay_mdts_report_requires_base
    (base_ok : Prop) (delta_ok : Prop)
    (projection_ok : Prop) (digest_guard : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMDTSTransportedModelReport
      (AyMDTSTransportEvidence
        base_ok delta_ok projection_ok digest_guard)
      audit_entry original_model ->
    base_ok := by
  intro report
  exact ay_mdts_transport_evidence_base
    base_ok delta_ok projection_ok digest_guard
    (ay_mdts_report_evidence
      (AyMDTSTransportEvidence
        base_ok delta_ok projection_ok digest_guard)
      audit_entry original_model report)

theorem ay_mdts_report_requires_delta
    (base_ok : Prop) (delta_ok : Prop)
    (projection_ok : Prop) (digest_guard : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMDTSTransportedModelReport
      (AyMDTSTransportEvidence
        base_ok delta_ok projection_ok digest_guard)
      audit_entry original_model ->
    delta_ok := by
  intro report
  exact ay_mdts_transport_evidence_delta
    base_ok delta_ok projection_ok digest_guard
    (ay_mdts_report_evidence
      (AyMDTSTransportEvidence
        base_ok delta_ok projection_ok digest_guard)
      audit_entry original_model report)

theorem ay_mdts_report_requires_projection
    (base_ok : Prop) (delta_ok : Prop)
    (projection_ok : Prop) (digest_guard : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMDTSTransportedModelReport
      (AyMDTSTransportEvidence
        base_ok delta_ok projection_ok digest_guard)
      audit_entry original_model ->
    projection_ok := by
  intro report
  exact ay_mdts_transport_evidence_projection
    base_ok delta_ok projection_ok digest_guard
    (ay_mdts_report_evidence
      (AyMDTSTransportEvidence
        base_ok delta_ok projection_ok digest_guard)
      audit_entry original_model report)

theorem ay_mdts_report_requires_digest
    (base_ok : Prop) (delta_ok : Prop)
    (projection_ok : Prop) (digest_guard : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMDTSTransportedModelReport
      (AyMDTSTransportEvidence
        base_ok delta_ok projection_ok digest_guard)
      audit_entry original_model ->
    digest_guard := by
  intro report
  exact ay_mdts_transport_evidence_digest
    base_ok delta_ok projection_ok digest_guard
    (ay_mdts_report_evidence
      (AyMDTSTransportEvidence
        base_ok delta_ok projection_ok digest_guard)
      audit_entry original_model report)

theorem ay_mdts_report_sound_exact
    (base_ok : Prop) (delta_ok : Prop)
    (projection_ok : Prop) (digest_guard : Prop)
    (audit_entry : Prop) (original_model : Prop) :
    AyMDTSEquisat
      (AyMDTSTransportedModelReport
        (AyMDTSTransportEvidence
          base_ok delta_ok projection_ok digest_guard)
        audit_entry original_model)
      (AyMDTSConj base_ok
        (AyMDTSConj delta_ok
          (AyMDTSConj projection_ok
            (AyMDTSConj digest_guard
              (AyMDTSConj audit_entry original_model))))) := by
  exact ay_mdts_equisat_intro
    (AyMDTSTransportedModelReport
      (AyMDTSTransportEvidence
        base_ok delta_ok projection_ok digest_guard)
      audit_entry original_model)
    (AyMDTSConj base_ok
      (AyMDTSConj delta_ok
        (AyMDTSConj projection_ok
          (AyMDTSConj digest_guard
            (AyMDTSConj audit_entry original_model)))))
    (fun report =>
      ay_mdts_conj_intro base_ok
        (AyMDTSConj delta_ok
          (AyMDTSConj projection_ok
            (AyMDTSConj digest_guard
              (AyMDTSConj audit_entry original_model))))
        (ay_mdts_report_requires_base
          base_ok delta_ok projection_ok digest_guard
          audit_entry original_model report)
        (ay_mdts_conj_intro delta_ok
          (AyMDTSConj projection_ok
            (AyMDTSConj digest_guard
              (AyMDTSConj audit_entry original_model)))
          (ay_mdts_report_requires_delta
            base_ok delta_ok projection_ok digest_guard
            audit_entry original_model report)
          (ay_mdts_conj_intro projection_ok
            (AyMDTSConj digest_guard
              (AyMDTSConj audit_entry original_model))
            (ay_mdts_report_requires_projection
              base_ok delta_ok projection_ok digest_guard
              audit_entry original_model report)
            (ay_mdts_conj_intro digest_guard
              (AyMDTSConj audit_entry original_model)
              (ay_mdts_report_requires_digest
                base_ok delta_ok projection_ok digest_guard
                audit_entry original_model report)
              (ay_mdts_conj_intro audit_entry original_model
                (ay_mdts_report_audit
                  (AyMDTSTransportEvidence
                    base_ok delta_ok projection_ok digest_guard)
                  audit_entry original_model report)
                (ay_mdts_report_original
                  (AyMDTSTransportEvidence
                    base_ok delta_ok projection_ok digest_guard)
                  audit_entry original_model report))))))
    (fun bundle =>
      ay_mdts_report_intro
        (AyMDTSTransportEvidence
          base_ok delta_ok projection_ok digest_guard)
        audit_entry original_model
        (ay_mdts_transport_evidence_intro
          base_ok delta_ok projection_ok digest_guard
          (ay_mdts_conj_left base_ok
            (AyMDTSConj delta_ok
              (AyMDTSConj projection_ok
                (AyMDTSConj digest_guard
                  (AyMDTSConj audit_entry original_model))))
            bundle)
          (ay_mdts_conj_left delta_ok
            (AyMDTSConj projection_ok
              (AyMDTSConj digest_guard
                (AyMDTSConj audit_entry original_model)))
            (ay_mdts_conj_right base_ok
              (AyMDTSConj delta_ok
                (AyMDTSConj projection_ok
                  (AyMDTSConj digest_guard
                    (AyMDTSConj audit_entry original_model))))
              bundle))
          (ay_mdts_conj_left projection_ok
            (AyMDTSConj digest_guard
              (AyMDTSConj audit_entry original_model))
            (ay_mdts_conj_right delta_ok
              (AyMDTSConj projection_ok
                (AyMDTSConj digest_guard
                  (AyMDTSConj audit_entry original_model)))
              (ay_mdts_conj_right base_ok
                (AyMDTSConj delta_ok
                  (AyMDTSConj projection_ok
                    (AyMDTSConj digest_guard
                      (AyMDTSConj audit_entry original_model))))
                bundle)))
          (ay_mdts_conj_left digest_guard
            (AyMDTSConj audit_entry original_model)
            (ay_mdts_conj_right projection_ok
              (AyMDTSConj digest_guard
                (AyMDTSConj audit_entry original_model))
              (ay_mdts_conj_right delta_ok
                (AyMDTSConj projection_ok
                  (AyMDTSConj digest_guard
                    (AyMDTSConj audit_entry original_model)))
                (ay_mdts_conj_right base_ok
                  (AyMDTSConj delta_ok
                    (AyMDTSConj projection_ok
                      (AyMDTSConj digest_guard
                        (AyMDTSConj audit_entry original_model))))
                  bundle)))))
        (ay_mdts_conj_left audit_entry original_model
          (ay_mdts_conj_right digest_guard
            (AyMDTSConj audit_entry original_model)
            (ay_mdts_conj_right projection_ok
              (AyMDTSConj digest_guard
                (AyMDTSConj audit_entry original_model))
              (ay_mdts_conj_right delta_ok
                (AyMDTSConj projection_ok
                  (AyMDTSConj digest_guard
                    (AyMDTSConj audit_entry original_model)))
                (ay_mdts_conj_right base_ok
                  (AyMDTSConj delta_ok
                    (AyMDTSConj projection_ok
                      (AyMDTSConj digest_guard
                        (AyMDTSConj audit_entry original_model))))
                  bundle)))))
        (ay_mdts_conj_right audit_entry original_model
          (ay_mdts_conj_right digest_guard
            (AyMDTSConj audit_entry original_model)
            (ay_mdts_conj_right projection_ok
              (AyMDTSConj digest_guard
                (AyMDTSConj audit_entry original_model))
              (ay_mdts_conj_right delta_ok
                (AyMDTSConj projection_ok
                  (AyMDTSConj digest_guard
                    (AyMDTSConj audit_entry original_model)))
                (ay_mdts_conj_right base_ok
                  (AyMDTSConj delta_ok
                    (AyMDTSConj projection_ok
                      (AyMDTSConj digest_guard
                        (AyMDTSConj audit_entry original_model))))
                  bundle))))))

theorem ay_mdts_no_claim_diagnostic_intro
    (diagnostic : Prop) (public_claim : Prop) :
    diagnostic ->
    (public_claim -> False) ->
    AyMDTSNoClaimDiagnostic diagnostic public_claim := by
  intro hdiagnostic
  intro blocks
  exact ay_mdts_conj_intro diagnostic
    (public_claim -> False) hdiagnostic blocks

theorem ay_mdts_no_claim_diagnostic_reason
    (diagnostic : Prop) (public_claim : Prop) :
    AyMDTSNoClaimDiagnostic diagnostic public_claim ->
    diagnostic := by
  intro diag
  exact ay_mdts_conj_left diagnostic (public_claim -> False) diag

theorem ay_mdts_no_claim_diagnostic_blocks
    (diagnostic : Prop) (public_claim : Prop) :
    AyMDTSNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  exact ay_mdts_conj_right diagnostic (public_claim -> False) diag

theorem ay_mdts_missing_delta_no_claim
    (missing_delta : Prop) (public_claim : Prop) :
    missing_delta ->
    (public_claim -> missing_delta -> False) ->
    AyMDTSNoClaimDiagnostic missing_delta public_claim := by
  intro hmissing
  intro blocks
  exact ay_mdts_no_claim_diagnostic_intro
    missing_delta public_claim
    hmissing
    (fun claim => blocks claim hmissing)

theorem ay_mdts_corrupt_delta_no_claim
    (corrupt_delta : Prop) (public_claim : Prop) :
    corrupt_delta ->
    (public_claim -> corrupt_delta -> False) ->
    AyMDTSNoClaimDiagnostic corrupt_delta public_claim := by
  intro hcorrupt
  intro blocks
  exact ay_mdts_no_claim_diagnostic_intro
    corrupt_delta public_claim
    hcorrupt
    (fun claim => blocks claim hcorrupt)

theorem ay_mdts_base_mismatch_no_claim
    (base_mismatch : Prop) (public_claim : Prop) :
    base_mismatch ->
    (public_claim -> base_mismatch -> False) ->
    AyMDTSNoClaimDiagnostic base_mismatch public_claim := by
  intro hmismatch
  intro blocks
  exact ay_mdts_no_claim_diagnostic_intro
    base_mismatch public_claim
    hmismatch
    (fun claim => blocks claim hmismatch)

theorem ay_mdts_digest_mismatch_no_claim
    (digest_mismatch : Prop) (public_claim : Prop) :
    digest_mismatch ->
    (public_claim -> digest_mismatch -> False) ->
    AyMDTSNoClaimDiagnostic digest_mismatch public_claim := by
  intro hmismatch
  intro blocks
  exact ay_mdts_no_claim_diagnostic_intro
    digest_mismatch public_claim
    hmismatch
    (fun claim => blocks claim hmismatch)

theorem ay_mdts_diagnostic_blocks_public_claim
    (diagnostic : Prop) (public_claim : Prop) :
    AyMDTSNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  intro claim
  exact ay_mdts_no_claim_diagnostic_blocks
    diagnostic public_claim diag claim

theorem ay_mdts_bad_delta_transport_no_stale_claim
    (missing_delta : Prop) (corrupt_delta : Prop)
    (public_claim : Prop) :
    AyMDTSDisj missing_delta corrupt_delta ->
    (public_claim -> missing_delta -> False) ->
    (public_claim -> corrupt_delta -> False) ->
    AyMDTSDisj
      (AyMDTSNoClaimDiagnostic missing_delta public_claim)
      (AyMDTSNoClaimDiagnostic corrupt_delta public_claim) := by
  intro bad_delta
  intro missing_blocks
  intro corrupt_blocks
  exact bad_delta
    (AyMDTSDisj
      (AyMDTSNoClaimDiagnostic missing_delta public_claim)
      (AyMDTSNoClaimDiagnostic corrupt_delta public_claim))
    (fun hmissing =>
      ay_mdts_disj_left
        (AyMDTSNoClaimDiagnostic missing_delta public_claim)
        (AyMDTSNoClaimDiagnostic corrupt_delta public_claim)
        (ay_mdts_missing_delta_no_claim
          missing_delta public_claim hmissing missing_blocks))
    (fun hcorrupt =>
      ay_mdts_disj_right
        (AyMDTSNoClaimDiagnostic missing_delta public_claim)
        (AyMDTSNoClaimDiagnostic corrupt_delta public_claim)
        (ay_mdts_corrupt_delta_no_claim
          corrupt_delta public_claim hcorrupt corrupt_blocks))
