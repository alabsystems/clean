-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for compressed model-assignment soundness.
-- Compressed or delta assignments justify public SAT reports exactly with
-- decompression, projection, manifest/digest, and audit/Merkle evidence.
-- Corrupt or missing chunks and digest mismatches are no-claim diagnostics.

def AyMACSConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMACSDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMACSEquisat (before : Prop) (after : Prop) :=
  AyMACSConj (before -> after) (after -> before)

def AyMACSManifestDigestGuard
    (manifest_ids : Prop) (digest_guard : Prop) :=
  AyMACSConj manifest_ids digest_guard

def AyMACSCompressedAssignment
    (compressed_chunks : Prop) (delta_chunks : Prop) :=
  AyMACSConj compressed_chunks delta_chunks

def AyMACSDecompressionWitness
    (compressed_assignment : Prop) (full_assignment : Prop) :=
  compressed_assignment -> full_assignment

def AyMACSProjectionToOriginal
    (full_assignment : Prop) (original_model : Prop) :=
  full_assignment -> original_model

def AyMACSCompressionEvidence
    (decompression_ok : Prop) (projection_ok : Prop)
    (manifest_guard : Prop) :=
  AyMACSConj decompression_ok
    (AyMACSConj projection_ok manifest_guard)

def AyMACSAuditMerkleEntry
    (audit_entry : Prop) (merkle_root : Prop) :=
  AyMACSConj audit_entry merkle_root

def AyMACSCompressedModelReport
    (compression_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :=
  AyMACSConj compression_evidence
    (AyMACSConj audit_merkle original_model)

def AyMACSNoClaimDiagnostic
    (diagnostic : Prop) (public_claim : Prop) :=
  AyMACSConj diagnostic (public_claim -> False)

theorem ay_macs_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMACSConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_macs_conj_left
    (left : Prop) (right : Prop) :
    AyMACSConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_macs_conj_right
    (left : Prop) (right : Prop) :
    AyMACSConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_macs_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMACSDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_macs_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMACSDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_macs_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMACSEquisat before after := by
  intro forward
  intro backward
  exact ay_macs_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_macs_equisat_forward
    (before : Prop) (after : Prop) :
    AyMACSEquisat before after -> before -> after := by
  intro certificate
  exact ay_macs_conj_left (before -> after) (after -> before) certificate

theorem ay_macs_equisat_backward
    (before : Prop) (after : Prop) :
    AyMACSEquisat before after -> after -> before := by
  intro certificate
  exact ay_macs_conj_right (before -> after) (after -> before) certificate

theorem ay_macs_manifest_digest_guard_intro
    (manifest_ids : Prop) (digest_guard : Prop) :
    manifest_ids ->
    digest_guard ->
    AyMACSManifestDigestGuard manifest_ids digest_guard := by
  intro hmanifest
  intro hdigest
  exact ay_macs_conj_intro manifest_ids digest_guard
    hmanifest hdigest

theorem ay_macs_manifest_digest_guard_manifest
    (manifest_ids : Prop) (digest_guard : Prop) :
    AyMACSManifestDigestGuard manifest_ids digest_guard ->
    manifest_ids := by
  intro guard
  exact ay_macs_conj_left manifest_ids digest_guard guard

theorem ay_macs_manifest_digest_guard_digest
    (manifest_ids : Prop) (digest_guard : Prop) :
    AyMACSManifestDigestGuard manifest_ids digest_guard ->
    digest_guard := by
  intro guard
  exact ay_macs_conj_right manifest_ids digest_guard guard

theorem ay_macs_compressed_assignment_intro
    (compressed_chunks : Prop) (delta_chunks : Prop) :
    compressed_chunks ->
    delta_chunks ->
    AyMACSCompressedAssignment compressed_chunks delta_chunks := by
  intro hcompressed
  intro hdelta
  exact ay_macs_conj_intro compressed_chunks delta_chunks
    hcompressed hdelta

theorem ay_macs_compressed_assignment_chunks
    (compressed_chunks : Prop) (delta_chunks : Prop) :
    AyMACSCompressedAssignment compressed_chunks delta_chunks ->
    compressed_chunks := by
  intro assignment
  exact ay_macs_conj_left compressed_chunks delta_chunks assignment

theorem ay_macs_compressed_assignment_delta
    (compressed_chunks : Prop) (delta_chunks : Prop) :
    AyMACSCompressedAssignment compressed_chunks delta_chunks ->
    delta_chunks := by
  intro assignment
  exact ay_macs_conj_right compressed_chunks delta_chunks assignment

theorem ay_macs_decompression_apply
    (compressed_assignment : Prop) (full_assignment : Prop) :
    AyMACSDecompressionWitness
      compressed_assignment full_assignment ->
    compressed_assignment ->
    full_assignment := by
  intro decompress
  intro hcompressed
  exact decompress hcompressed

theorem ay_macs_projection_apply
    (full_assignment : Prop) (original_model : Prop) :
    AyMACSProjectionToOriginal full_assignment original_model ->
    full_assignment ->
    original_model := by
  intro project
  intro hfull
  exact project hfull

theorem ay_macs_compression_evidence_intro
    (decompression_ok : Prop) (projection_ok : Prop)
    (manifest_guard : Prop) :
    decompression_ok ->
    projection_ok ->
    manifest_guard ->
    AyMACSCompressionEvidence
      decompression_ok projection_ok manifest_guard := by
  intro hdecompress
  intro hproject
  intro hguard
  exact ay_macs_conj_intro decompression_ok
    (AyMACSConj projection_ok manifest_guard)
    hdecompress
    (ay_macs_conj_intro projection_ok manifest_guard
      hproject hguard)

theorem ay_macs_compression_evidence_decompression
    (decompression_ok : Prop) (projection_ok : Prop)
    (manifest_guard : Prop) :
    AyMACSCompressionEvidence
      decompression_ok projection_ok manifest_guard ->
    decompression_ok := by
  intro evidence
  exact ay_macs_conj_left decompression_ok
    (AyMACSConj projection_ok manifest_guard) evidence

theorem ay_macs_compression_evidence_projection
    (decompression_ok : Prop) (projection_ok : Prop)
    (manifest_guard : Prop) :
    AyMACSCompressionEvidence
      decompression_ok projection_ok manifest_guard ->
    projection_ok := by
  intro evidence
  exact ay_macs_conj_left projection_ok manifest_guard
    (ay_macs_conj_right decompression_ok
      (AyMACSConj projection_ok manifest_guard) evidence)

theorem ay_macs_compression_evidence_guard
    (decompression_ok : Prop) (projection_ok : Prop)
    (manifest_guard : Prop) :
    AyMACSCompressionEvidence
      decompression_ok projection_ok manifest_guard ->
    manifest_guard := by
  intro evidence
  exact ay_macs_conj_right projection_ok manifest_guard
    (ay_macs_conj_right decompression_ok
      (AyMACSConj projection_ok manifest_guard) evidence)

theorem ay_macs_audit_merkle_intro
    (audit_entry : Prop) (merkle_root : Prop) :
    audit_entry ->
    merkle_root ->
    AyMACSAuditMerkleEntry audit_entry merkle_root := by
  intro haudit
  intro hroot
  exact ay_macs_conj_intro audit_entry merkle_root
    haudit hroot

theorem ay_macs_audit_merkle_entry
    (audit_entry : Prop) (merkle_root : Prop) :
    AyMACSAuditMerkleEntry audit_entry merkle_root ->
    audit_entry := by
  intro audit
  exact ay_macs_conj_left audit_entry merkle_root audit

theorem ay_macs_audit_merkle_root
    (audit_entry : Prop) (merkle_root : Prop) :
    AyMACSAuditMerkleEntry audit_entry merkle_root ->
    merkle_root := by
  intro audit
  exact ay_macs_conj_right audit_entry merkle_root audit

theorem ay_macs_report_intro
    (compression_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    compression_evidence ->
    audit_merkle ->
    original_model ->
    AyMACSCompressedModelReport
      compression_evidence audit_merkle original_model := by
  intro hevidence
  intro haudit
  intro horiginal
  exact ay_macs_conj_intro compression_evidence
    (AyMACSConj audit_merkle original_model)
    hevidence
    (ay_macs_conj_intro audit_merkle original_model
      haudit horiginal)

theorem ay_macs_report_evidence
    (compression_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMACSCompressedModelReport
      compression_evidence audit_merkle original_model ->
    compression_evidence := by
  intro report
  exact ay_macs_conj_left compression_evidence
    (AyMACSConj audit_merkle original_model) report

theorem ay_macs_report_audit
    (compression_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMACSCompressedModelReport
      compression_evidence audit_merkle original_model ->
    audit_merkle := by
  intro report
  exact ay_macs_conj_left audit_merkle original_model
    (ay_macs_conj_right compression_evidence
      (AyMACSConj audit_merkle original_model) report)

theorem ay_macs_report_original
    (compression_evidence : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMACSCompressedModelReport
      compression_evidence audit_merkle original_model ->
    original_model := by
  intro report
  exact ay_macs_conj_right audit_merkle original_model
    (ay_macs_conj_right compression_evidence
      (AyMACSConj audit_merkle original_model) report)

theorem ay_macs_decompressed_original_model
    (compressed_assignment : Prop) (full_assignment : Prop)
    (original_model : Prop) :
    AyMACSDecompressionWitness
      compressed_assignment full_assignment ->
    AyMACSProjectionToOriginal full_assignment original_model ->
    compressed_assignment ->
    original_model := by
  intro decompress
  intro project
  intro hcompressed
  exact project (decompress hcompressed)

theorem ay_macs_compressed_assignment_original_model
    (compressed_chunks : Prop) (delta_chunks : Prop)
    (full_assignment : Prop) (original_model : Prop) :
    AyMACSDecompressionWitness
      (AyMACSCompressedAssignment
        compressed_chunks delta_chunks)
      full_assignment ->
    AyMACSProjectionToOriginal full_assignment original_model ->
    AyMACSCompressedAssignment compressed_chunks delta_chunks ->
    original_model := by
  intro decompress
  intro project
  intro assignment
  exact project (decompress assignment)

theorem ay_macs_compressed_report_from_evidence
    (compressed_assignment : Prop) (full_assignment : Prop)
    (original_model : Prop) (decompression_ok : Prop)
    (projection_ok : Prop) (manifest_guard : Prop)
    (audit_merkle : Prop) :
    AyMACSDecompressionWitness
      compressed_assignment full_assignment ->
    AyMACSProjectionToOriginal full_assignment original_model ->
    compressed_assignment ->
    decompression_ok ->
    projection_ok ->
    manifest_guard ->
    audit_merkle ->
    AyMACSCompressedModelReport
      (AyMACSCompressionEvidence
        decompression_ok projection_ok manifest_guard)
      audit_merkle original_model := by
  intro decompress
  intro project
  intro hcompressed
  intro hdecompress
  intro hproject
  intro hguard
  intro haudit
  exact ay_macs_report_intro
    (AyMACSCompressionEvidence
      decompression_ok projection_ok manifest_guard)
    audit_merkle original_model
    (ay_macs_compression_evidence_intro
      decompression_ok projection_ok manifest_guard
      hdecompress hproject hguard)
    haudit
    (project (decompress hcompressed))

theorem ay_macs_report_requires_decompression
    (decompression_ok : Prop) (projection_ok : Prop)
    (manifest_guard : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMACSCompressedModelReport
      (AyMACSCompressionEvidence
        decompression_ok projection_ok manifest_guard)
      audit_merkle original_model ->
    decompression_ok := by
  intro report
  exact ay_macs_compression_evidence_decompression
    decompression_ok projection_ok manifest_guard
    (ay_macs_report_evidence
      (AyMACSCompressionEvidence
        decompression_ok projection_ok manifest_guard)
      audit_merkle original_model report)

theorem ay_macs_report_requires_projection
    (decompression_ok : Prop) (projection_ok : Prop)
    (manifest_guard : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMACSCompressedModelReport
      (AyMACSCompressionEvidence
        decompression_ok projection_ok manifest_guard)
      audit_merkle original_model ->
    projection_ok := by
  intro report
  exact ay_macs_compression_evidence_projection
    decompression_ok projection_ok manifest_guard
    (ay_macs_report_evidence
      (AyMACSCompressionEvidence
        decompression_ok projection_ok manifest_guard)
      audit_merkle original_model report)

theorem ay_macs_report_requires_manifest_digest
    (decompression_ok : Prop) (projection_ok : Prop)
    (manifest_guard : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMACSCompressedModelReport
      (AyMACSCompressionEvidence
        decompression_ok projection_ok manifest_guard)
      audit_merkle original_model ->
    manifest_guard := by
  intro report
  exact ay_macs_compression_evidence_guard
    decompression_ok projection_ok manifest_guard
    (ay_macs_report_evidence
      (AyMACSCompressionEvidence
        decompression_ok projection_ok manifest_guard)
      audit_merkle original_model report)

theorem ay_macs_report_sound_exact
    (decompression_ok : Prop) (projection_ok : Prop)
    (manifest_guard : Prop) (audit_merkle : Prop)
    (original_model : Prop) :
    AyMACSEquisat
      (AyMACSCompressedModelReport
        (AyMACSCompressionEvidence
          decompression_ok projection_ok manifest_guard)
        audit_merkle original_model)
      (AyMACSConj decompression_ok
        (AyMACSConj projection_ok
          (AyMACSConj manifest_guard
            (AyMACSConj audit_merkle original_model)))) := by
  exact ay_macs_equisat_intro
    (AyMACSCompressedModelReport
      (AyMACSCompressionEvidence
        decompression_ok projection_ok manifest_guard)
      audit_merkle original_model)
    (AyMACSConj decompression_ok
      (AyMACSConj projection_ok
        (AyMACSConj manifest_guard
          (AyMACSConj audit_merkle original_model))))
    (fun report =>
      ay_macs_conj_intro decompression_ok
        (AyMACSConj projection_ok
          (AyMACSConj manifest_guard
            (AyMACSConj audit_merkle original_model)))
        (ay_macs_report_requires_decompression
          decompression_ok projection_ok manifest_guard
          audit_merkle original_model report)
        (ay_macs_conj_intro projection_ok
          (AyMACSConj manifest_guard
            (AyMACSConj audit_merkle original_model))
          (ay_macs_report_requires_projection
            decompression_ok projection_ok manifest_guard
            audit_merkle original_model report)
          (ay_macs_conj_intro manifest_guard
            (AyMACSConj audit_merkle original_model)
            (ay_macs_report_requires_manifest_digest
              decompression_ok projection_ok manifest_guard
              audit_merkle original_model report)
            (ay_macs_conj_intro audit_merkle original_model
              (ay_macs_report_audit
                (AyMACSCompressionEvidence
                  decompression_ok projection_ok manifest_guard)
                audit_merkle original_model report)
              (ay_macs_report_original
                (AyMACSCompressionEvidence
                  decompression_ok projection_ok manifest_guard)
                audit_merkle original_model report)))))
    (fun bundle =>
      ay_macs_report_intro
        (AyMACSCompressionEvidence
          decompression_ok projection_ok manifest_guard)
        audit_merkle original_model
        (ay_macs_compression_evidence_intro
          decompression_ok projection_ok manifest_guard
          (ay_macs_conj_left decompression_ok
            (AyMACSConj projection_ok
              (AyMACSConj manifest_guard
                (AyMACSConj audit_merkle original_model)))
            bundle)
          (ay_macs_conj_left projection_ok
            (AyMACSConj manifest_guard
              (AyMACSConj audit_merkle original_model))
            (ay_macs_conj_right decompression_ok
              (AyMACSConj projection_ok
                (AyMACSConj manifest_guard
                  (AyMACSConj audit_merkle original_model)))
              bundle))
          (ay_macs_conj_left manifest_guard
            (AyMACSConj audit_merkle original_model)
            (ay_macs_conj_right projection_ok
              (AyMACSConj manifest_guard
                (AyMACSConj audit_merkle original_model))
              (ay_macs_conj_right decompression_ok
                (AyMACSConj projection_ok
                  (AyMACSConj manifest_guard
                    (AyMACSConj audit_merkle original_model)))
                bundle))))
        (ay_macs_conj_left audit_merkle original_model
          (ay_macs_conj_right manifest_guard
            (AyMACSConj audit_merkle original_model)
            (ay_macs_conj_right projection_ok
              (AyMACSConj manifest_guard
                (AyMACSConj audit_merkle original_model))
              (ay_macs_conj_right decompression_ok
                (AyMACSConj projection_ok
                  (AyMACSConj manifest_guard
                    (AyMACSConj audit_merkle original_model)))
                bundle))))
        (ay_macs_conj_right audit_merkle original_model
          (ay_macs_conj_right manifest_guard
            (AyMACSConj audit_merkle original_model)
            (ay_macs_conj_right projection_ok
              (AyMACSConj manifest_guard
                (AyMACSConj audit_merkle original_model))
              (ay_macs_conj_right decompression_ok
                (AyMACSConj projection_ok
                  (AyMACSConj manifest_guard
                    (AyMACSConj audit_merkle original_model)))
                bundle)))))

theorem ay_macs_no_claim_diagnostic_intro
    (diagnostic : Prop) (public_claim : Prop) :
    diagnostic ->
    (public_claim -> False) ->
    AyMACSNoClaimDiagnostic diagnostic public_claim := by
  intro hdiagnostic
  intro blocks
  exact ay_macs_conj_intro diagnostic
    (public_claim -> False) hdiagnostic blocks

theorem ay_macs_no_claim_diagnostic_reason
    (diagnostic : Prop) (public_claim : Prop) :
    AyMACSNoClaimDiagnostic diagnostic public_claim ->
    diagnostic := by
  intro diag
  exact ay_macs_conj_left diagnostic (public_claim -> False) diag

theorem ay_macs_no_claim_diagnostic_blocks
    (diagnostic : Prop) (public_claim : Prop) :
    AyMACSNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  exact ay_macs_conj_right diagnostic (public_claim -> False) diag

theorem ay_macs_corrupt_chunk_no_claim
    (corrupt_chunk : Prop) (public_claim : Prop) :
    corrupt_chunk ->
    (public_claim -> corrupt_chunk -> False) ->
    AyMACSNoClaimDiagnostic corrupt_chunk public_claim := by
  intro hcorrupt
  intro blocks
  exact ay_macs_no_claim_diagnostic_intro
    corrupt_chunk public_claim
    hcorrupt
    (fun claim => blocks claim hcorrupt)

theorem ay_macs_missing_chunk_no_claim
    (missing_chunk : Prop) (public_claim : Prop) :
    missing_chunk ->
    (public_claim -> missing_chunk -> False) ->
    AyMACSNoClaimDiagnostic missing_chunk public_claim := by
  intro hmissing
  intro blocks
  exact ay_macs_no_claim_diagnostic_intro
    missing_chunk public_claim
    hmissing
    (fun claim => blocks claim hmissing)

theorem ay_macs_digest_mismatch_no_claim
    (digest_mismatch : Prop) (public_claim : Prop) :
    digest_mismatch ->
    (public_claim -> digest_mismatch -> False) ->
    AyMACSNoClaimDiagnostic digest_mismatch public_claim := by
  intro hmismatch
  intro blocks
  exact ay_macs_no_claim_diagnostic_intro
    digest_mismatch public_claim
    hmismatch
    (fun claim => blocks claim hmismatch)

theorem ay_macs_decompression_failure_no_claim
    (decompression_failure : Prop) (public_claim : Prop) :
    decompression_failure ->
    (public_claim -> decompression_failure -> False) ->
    AyMACSNoClaimDiagnostic
      decompression_failure public_claim := by
  intro hfailure
  intro blocks
  exact ay_macs_no_claim_diagnostic_intro
    decompression_failure public_claim
    hfailure
    (fun claim => blocks claim hfailure)

theorem ay_macs_diagnostic_blocks_public_claim
    (diagnostic : Prop) (public_claim : Prop) :
    AyMACSNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  intro claim
  exact ay_macs_no_claim_diagnostic_blocks
    diagnostic public_claim diag claim

theorem ay_macs_bad_compression_no_stale_claim
    (corrupt_chunk : Prop) (missing_chunk : Prop)
    (public_claim : Prop) :
    AyMACSDisj corrupt_chunk missing_chunk ->
    (public_claim -> corrupt_chunk -> False) ->
    (public_claim -> missing_chunk -> False) ->
    AyMACSDisj
      (AyMACSNoClaimDiagnostic corrupt_chunk public_claim)
      (AyMACSNoClaimDiagnostic missing_chunk public_claim) := by
  intro bad
  intro corrupt_blocks
  intro missing_blocks
  exact bad
    (AyMACSDisj
      (AyMACSNoClaimDiagnostic corrupt_chunk public_claim)
      (AyMACSNoClaimDiagnostic missing_chunk public_claim))
    (fun hcorrupt =>
      ay_macs_disj_left
        (AyMACSNoClaimDiagnostic corrupt_chunk public_claim)
        (AyMACSNoClaimDiagnostic missing_chunk public_claim)
        (ay_macs_corrupt_chunk_no_claim
          corrupt_chunk public_claim hcorrupt corrupt_blocks))
    (fun hmissing =>
      ay_macs_disj_right
        (AyMACSNoClaimDiagnostic corrupt_chunk public_claim)
        (AyMACSNoClaimDiagnostic missing_chunk public_claim)
        (ay_macs_missing_chunk_no_claim
          missing_chunk public_claim hmissing missing_blocks))

