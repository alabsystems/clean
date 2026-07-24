-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for partial-assignment extension soundness.
-- Inprocessing/cube/assumption partial assignments become public full models
-- only when coverage, defaults, extension map, frame, reconstruction, and
-- checker evidence agree. Bad partials are no-claim/recompute facts.

def AyMPAEConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMPAEDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMPAEquisat (before : Prop) (after : Prop) :=
  AyMPAEConj (before -> after) (after -> before)

def AyMPAEPartialAssignment
    (assigned_domain : Prop) (assigned_values : Prop) :=
  AyMPAEConj assigned_domain assigned_values

def AyMPAEDomainCoverage
    (partial_domain : Prop) (visible_domain : Prop) :=
  AyMPAEConj partial_domain visible_domain

def AyMPAEDefaultExtension
    (default_assignment : Prop) (extension_map : Prop) :=
  AyMPAEConj default_assignment extension_map

def AyMPAEAssumptionFrame
    (cube_frame : Prop) (assumption_frame : Prop) :=
  AyMPAEConj cube_frame assumption_frame

def AyMPAEExtensionWitness
    (partial_assignment : Prop) (full_assignment : Prop) :=
  partial_assignment -> full_assignment

def AyMPAEFormulaReconstruction
    (full_assignment : Prop) (original_model : Prop) :=
  full_assignment -> original_model

def AyMPAEExtensionEvidence
    (coverage_ok : Prop) (defaults_ok : Prop)
    (frame_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :=
  AyMPAEConj coverage_ok
    (AyMPAEConj defaults_ok
      (AyMPAEConj frame_ok
        (AyMPAEConj reconstruction_ok checker_ok)))

def AyMPAEAcceptedSatReport
    (extension_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :=
  AyMPAEConj extension_evidence
    (AyMPAEConj audit_entry original_model)

def AyMPAENoClaimDiagnostic
    (diagnostic : Prop) (public_claim : Prop) :=
  AyMPAEConj diagnostic (public_claim -> False)

def AyMPAERecomputeObligation
    (reason : Prop) (recompute_request : Prop) :=
  AyMPAEConj reason recompute_request

theorem ay_mpae_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMPAEConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mpae_conj_left
    (left : Prop) (right : Prop) :
    AyMPAEConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mpae_conj_right
    (left : Prop) (right : Prop) :
    AyMPAEConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mpae_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMPAEDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mpae_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMPAEDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mpae_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMPAEquisat before after := by
  intro forward
  intro backward
  exact ay_mpae_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_mpae_equisat_forward
    (before : Prop) (after : Prop) :
    AyMPAEquisat before after -> before -> after := by
  intro certificate
  exact ay_mpae_conj_left (before -> after) (after -> before) certificate

theorem ay_mpae_equisat_backward
    (before : Prop) (after : Prop) :
    AyMPAEquisat before after -> after -> before := by
  intro certificate
  exact ay_mpae_conj_right (before -> after) (after -> before) certificate

theorem ay_mpae_partial_assignment_intro
    (assigned_domain : Prop) (assigned_values : Prop) :
    assigned_domain ->
    assigned_values ->
    AyMPAEPartialAssignment assigned_domain assigned_values := by
  intro hdomain
  intro hvalues
  exact ay_mpae_conj_intro assigned_domain assigned_values
    hdomain hvalues

theorem ay_mpae_partial_assignment_domain
    (assigned_domain : Prop) (assigned_values : Prop) :
    AyMPAEPartialAssignment assigned_domain assigned_values ->
    assigned_domain := by
  intro assignment
  exact ay_mpae_conj_left assigned_domain assigned_values assignment

theorem ay_mpae_partial_assignment_values
    (assigned_domain : Prop) (assigned_values : Prop) :
    AyMPAEPartialAssignment assigned_domain assigned_values ->
    assigned_values := by
  intro assignment
  exact ay_mpae_conj_right assigned_domain assigned_values assignment

theorem ay_mpae_domain_coverage_intro
    (partial_domain : Prop) (visible_domain : Prop) :
    partial_domain ->
    visible_domain ->
    AyMPAEDomainCoverage partial_domain visible_domain := by
  intro hpartial
  intro hvisible
  exact ay_mpae_conj_intro partial_domain visible_domain
    hpartial hvisible

theorem ay_mpae_domain_coverage_partial
    (partial_domain : Prop) (visible_domain : Prop) :
    AyMPAEDomainCoverage partial_domain visible_domain ->
    partial_domain := by
  intro coverage
  exact ay_mpae_conj_left partial_domain visible_domain coverage

theorem ay_mpae_domain_coverage_visible
    (partial_domain : Prop) (visible_domain : Prop) :
    AyMPAEDomainCoverage partial_domain visible_domain ->
    visible_domain := by
  intro coverage
  exact ay_mpae_conj_right partial_domain visible_domain coverage

theorem ay_mpae_default_extension_intro
    (default_assignment : Prop) (extension_map : Prop) :
    default_assignment ->
    extension_map ->
    AyMPAEDefaultExtension default_assignment extension_map := by
  intro hdefault
  intro hmap
  exact ay_mpae_conj_intro default_assignment extension_map
    hdefault hmap

theorem ay_mpae_default_extension_default
    (default_assignment : Prop) (extension_map : Prop) :
    AyMPAEDefaultExtension default_assignment extension_map ->
    default_assignment := by
  intro extension
  exact ay_mpae_conj_left default_assignment extension_map extension

theorem ay_mpae_default_extension_map
    (default_assignment : Prop) (extension_map : Prop) :
    AyMPAEDefaultExtension default_assignment extension_map ->
    extension_map := by
  intro extension
  exact ay_mpae_conj_right default_assignment extension_map extension

theorem ay_mpae_assumption_frame_intro
    (cube_frame : Prop) (assumption_frame : Prop) :
    cube_frame ->
    assumption_frame ->
    AyMPAEAssumptionFrame cube_frame assumption_frame := by
  intro hcube
  intro hassumption
  exact ay_mpae_conj_intro cube_frame assumption_frame
    hcube hassumption

theorem ay_mpae_assumption_frame_cube
    (cube_frame : Prop) (assumption_frame : Prop) :
    AyMPAEAssumptionFrame cube_frame assumption_frame ->
    cube_frame := by
  intro frame
  exact ay_mpae_conj_left cube_frame assumption_frame frame

theorem ay_mpae_assumption_frame_assumption
    (cube_frame : Prop) (assumption_frame : Prop) :
    AyMPAEAssumptionFrame cube_frame assumption_frame ->
    assumption_frame := by
  intro frame
  exact ay_mpae_conj_right cube_frame assumption_frame frame

theorem ay_mpae_extension_apply
    (partial_assignment : Prop) (full_assignment : Prop) :
    AyMPAEExtensionWitness partial_assignment full_assignment ->
    partial_assignment ->
    full_assignment := by
  intro extend
  intro hpartial
  exact extend hpartial

theorem ay_mpae_formula_reconstruct_apply
    (full_assignment : Prop) (original_model : Prop) :
    AyMPAEFormulaReconstruction full_assignment original_model ->
    full_assignment ->
    original_model := by
  intro reconstruct
  intro hfull
  exact reconstruct hfull

theorem ay_mpae_extension_evidence_intro
    (coverage_ok : Prop) (defaults_ok : Prop)
    (frame_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :
    coverage_ok ->
    defaults_ok ->
    frame_ok ->
    reconstruction_ok ->
    checker_ok ->
    AyMPAEExtensionEvidence
      coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok := by
  intro hcoverage
  intro hdefaults
  intro hframe
  intro hreconstruct
  intro hchecker
  exact ay_mpae_conj_intro coverage_ok
    (AyMPAEConj defaults_ok
      (AyMPAEConj frame_ok
        (AyMPAEConj reconstruction_ok checker_ok)))
    hcoverage
    (ay_mpae_conj_intro defaults_ok
      (AyMPAEConj frame_ok
        (AyMPAEConj reconstruction_ok checker_ok))
      hdefaults
      (ay_mpae_conj_intro frame_ok
        (AyMPAEConj reconstruction_ok checker_ok)
        hframe
        (ay_mpae_conj_intro reconstruction_ok checker_ok
          hreconstruct hchecker)))

theorem ay_mpae_extension_evidence_coverage
    (coverage_ok : Prop) (defaults_ok : Prop)
    (frame_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :
    AyMPAEExtensionEvidence
      coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok ->
    coverage_ok := by
  intro evidence
  exact ay_mpae_conj_left coverage_ok
    (AyMPAEConj defaults_ok
      (AyMPAEConj frame_ok
        (AyMPAEConj reconstruction_ok checker_ok))) evidence

theorem ay_mpae_extension_evidence_defaults
    (coverage_ok : Prop) (defaults_ok : Prop)
    (frame_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :
    AyMPAEExtensionEvidence
      coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok ->
    defaults_ok := by
  intro evidence
  exact ay_mpae_conj_left defaults_ok
    (AyMPAEConj frame_ok
      (AyMPAEConj reconstruction_ok checker_ok))
    (ay_mpae_conj_right coverage_ok
      (AyMPAEConj defaults_ok
        (AyMPAEConj frame_ok
          (AyMPAEConj reconstruction_ok checker_ok))) evidence)

theorem ay_mpae_extension_evidence_frame
    (coverage_ok : Prop) (defaults_ok : Prop)
    (frame_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :
    AyMPAEExtensionEvidence
      coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok ->
    frame_ok := by
  intro evidence
  exact ay_mpae_conj_left frame_ok
    (AyMPAEConj reconstruction_ok checker_ok)
    (ay_mpae_conj_right defaults_ok
      (AyMPAEConj frame_ok
        (AyMPAEConj reconstruction_ok checker_ok))
      (ay_mpae_conj_right coverage_ok
        (AyMPAEConj defaults_ok
          (AyMPAEConj frame_ok
            (AyMPAEConj reconstruction_ok checker_ok))) evidence))

theorem ay_mpae_extension_evidence_reconstruction
    (coverage_ok : Prop) (defaults_ok : Prop)
    (frame_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :
    AyMPAEExtensionEvidence
      coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok ->
    reconstruction_ok := by
  intro evidence
  exact ay_mpae_conj_left reconstruction_ok checker_ok
    (ay_mpae_conj_right frame_ok
      (AyMPAEConj reconstruction_ok checker_ok)
      (ay_mpae_conj_right defaults_ok
        (AyMPAEConj frame_ok
          (AyMPAEConj reconstruction_ok checker_ok))
        (ay_mpae_conj_right coverage_ok
          (AyMPAEConj defaults_ok
            (AyMPAEConj frame_ok
              (AyMPAEConj reconstruction_ok checker_ok))) evidence)))

theorem ay_mpae_extension_evidence_checker
    (coverage_ok : Prop) (defaults_ok : Prop)
    (frame_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :
    AyMPAEExtensionEvidence
      coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok ->
    checker_ok := by
  intro evidence
  exact ay_mpae_conj_right reconstruction_ok checker_ok
    (ay_mpae_conj_right frame_ok
      (AyMPAEConj reconstruction_ok checker_ok)
      (ay_mpae_conj_right defaults_ok
        (AyMPAEConj frame_ok
          (AyMPAEConj reconstruction_ok checker_ok))
        (ay_mpae_conj_right coverage_ok
          (AyMPAEConj defaults_ok
            (AyMPAEConj frame_ok
              (AyMPAEConj reconstruction_ok checker_ok))) evidence)))

theorem ay_mpae_report_intro
    (extension_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    extension_evidence ->
    audit_entry ->
    original_model ->
    AyMPAEAcceptedSatReport
      extension_evidence audit_entry original_model := by
  intro hevidence
  intro haudit
  intro horiginal
  exact ay_mpae_conj_intro extension_evidence
    (AyMPAEConj audit_entry original_model)
    hevidence
    (ay_mpae_conj_intro audit_entry original_model haudit horiginal)

theorem ay_mpae_report_evidence
    (extension_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMPAEAcceptedSatReport
      extension_evidence audit_entry original_model ->
    extension_evidence := by
  intro report
  exact ay_mpae_conj_left extension_evidence
    (AyMPAEConj audit_entry original_model) report

theorem ay_mpae_report_audit
    (extension_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMPAEAcceptedSatReport
      extension_evidence audit_entry original_model ->
    audit_entry := by
  intro report
  exact ay_mpae_conj_left audit_entry original_model
    (ay_mpae_conj_right extension_evidence
      (AyMPAEConj audit_entry original_model) report)

theorem ay_mpae_report_original
    (extension_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMPAEAcceptedSatReport
      extension_evidence audit_entry original_model ->
    original_model := by
  intro report
  exact ay_mpae_conj_right audit_entry original_model
    (ay_mpae_conj_right extension_evidence
      (AyMPAEConj audit_entry original_model) report)

theorem ay_mpae_extended_original_model
    (partial_assignment : Prop) (full_assignment : Prop)
    (original_model : Prop) :
    AyMPAEExtensionWitness partial_assignment full_assignment ->
    AyMPAEFormulaReconstruction full_assignment original_model ->
    partial_assignment ->
    original_model := by
  intro extend
  intro reconstruct
  intro hpartial
  exact reconstruct (extend hpartial)

theorem ay_mpae_extended_report_from_evidence
    (partial_assignment : Prop) (full_assignment : Prop)
    (original_model : Prop) (coverage_ok : Prop)
    (defaults_ok : Prop) (frame_ok : Prop)
    (reconstruction_ok : Prop) (checker_ok : Prop)
    (audit_entry : Prop) :
    AyMPAEExtensionWitness partial_assignment full_assignment ->
    AyMPAEFormulaReconstruction full_assignment original_model ->
    partial_assignment ->
    coverage_ok ->
    defaults_ok ->
    frame_ok ->
    reconstruction_ok ->
    checker_ok ->
    audit_entry ->
    AyMPAEAcceptedSatReport
      (AyMPAEExtensionEvidence
        coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
      audit_entry original_model := by
  intro extend
  intro reconstruct
  intro hpartial
  intro hcoverage
  intro hdefaults
  intro hframe
  intro hreconstruction
  intro hchecker
  intro haudit
  exact ay_mpae_report_intro
    (AyMPAEExtensionEvidence
      coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
    audit_entry original_model
    (ay_mpae_extension_evidence_intro
      coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok
      hcoverage hdefaults hframe hreconstruction hchecker)
    haudit
    (reconstruct (extend hpartial))

theorem ay_mpae_report_requires_coverage
    (coverage_ok : Prop) (defaults_ok : Prop)
    (frame_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMPAEAcceptedSatReport
      (AyMPAEExtensionEvidence
        coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
      audit_entry original_model ->
    coverage_ok := by
  intro report
  exact ay_mpae_extension_evidence_coverage
    coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok
    (ay_mpae_report_evidence
      (AyMPAEExtensionEvidence
        coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
      audit_entry original_model report)

theorem ay_mpae_report_requires_defaults
    (coverage_ok : Prop) (defaults_ok : Prop)
    (frame_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMPAEAcceptedSatReport
      (AyMPAEExtensionEvidence
        coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
      audit_entry original_model ->
    defaults_ok := by
  intro report
  exact ay_mpae_extension_evidence_defaults
    coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok
    (ay_mpae_report_evidence
      (AyMPAEExtensionEvidence
        coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
      audit_entry original_model report)

theorem ay_mpae_report_requires_frame
    (coverage_ok : Prop) (defaults_ok : Prop)
    (frame_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMPAEAcceptedSatReport
      (AyMPAEExtensionEvidence
        coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
      audit_entry original_model ->
    frame_ok := by
  intro report
  exact ay_mpae_extension_evidence_frame
    coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok
    (ay_mpae_report_evidence
      (AyMPAEExtensionEvidence
        coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
      audit_entry original_model report)

theorem ay_mpae_report_requires_reconstruction
    (coverage_ok : Prop) (defaults_ok : Prop)
    (frame_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMPAEAcceptedSatReport
      (AyMPAEExtensionEvidence
        coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
      audit_entry original_model ->
    reconstruction_ok := by
  intro report
  exact ay_mpae_extension_evidence_reconstruction
    coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok
    (ay_mpae_report_evidence
      (AyMPAEExtensionEvidence
        coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
      audit_entry original_model report)

theorem ay_mpae_report_requires_checker
    (coverage_ok : Prop) (defaults_ok : Prop)
    (frame_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMPAEAcceptedSatReport
      (AyMPAEExtensionEvidence
        coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
      audit_entry original_model ->
    checker_ok := by
  intro report
  exact ay_mpae_extension_evidence_checker
    coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok
    (ay_mpae_report_evidence
      (AyMPAEExtensionEvidence
        coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
      audit_entry original_model report)

theorem ay_mpae_report_sound_exact
    (coverage_ok : Prop) (defaults_ok : Prop)
    (frame_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMPAEquisat
      (AyMPAEAcceptedSatReport
        (AyMPAEExtensionEvidence
          coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
        audit_entry original_model)
      (AyMPAEConj
        (AyMPAEExtensionEvidence
          coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
        (AyMPAEConj audit_entry original_model)) := by
  exact ay_mpae_equisat_intro
    (AyMPAEAcceptedSatReport
      (AyMPAEExtensionEvidence
        coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
      audit_entry original_model)
    (AyMPAEConj
      (AyMPAEExtensionEvidence
        coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
      (AyMPAEConj audit_entry original_model))
    (fun report =>
      ay_mpae_conj_intro
        (AyMPAEExtensionEvidence
          coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
        (AyMPAEConj audit_entry original_model)
        (ay_mpae_report_evidence
          (AyMPAEExtensionEvidence
            coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
          audit_entry original_model report)
        (ay_mpae_conj_intro audit_entry original_model
          (ay_mpae_report_audit
            (AyMPAEExtensionEvidence
              coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
            audit_entry original_model report)
          (ay_mpae_report_original
            (AyMPAEExtensionEvidence
              coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
            audit_entry original_model report)))
    (fun bundle =>
      ay_mpae_report_intro
        (AyMPAEExtensionEvidence
          coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
        audit_entry original_model
        (ay_mpae_conj_left
          (AyMPAEExtensionEvidence
            coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
          (AyMPAEConj audit_entry original_model)
          bundle)
        (ay_mpae_conj_left audit_entry original_model
          (ay_mpae_conj_right
            (AyMPAEExtensionEvidence
              coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
            (AyMPAEConj audit_entry original_model)
            bundle))
        (ay_mpae_conj_right audit_entry original_model
          (ay_mpae_conj_right
            (AyMPAEExtensionEvidence
              coverage_ok defaults_ok frame_ok reconstruction_ok checker_ok)
            (AyMPAEConj audit_entry original_model)
            bundle)))

theorem ay_mpae_no_claim_diagnostic_intro
    (diagnostic : Prop) (public_claim : Prop) :
    diagnostic ->
    (public_claim -> False) ->
    AyMPAENoClaimDiagnostic diagnostic public_claim := by
  intro hdiagnostic
  intro blocks
  exact ay_mpae_conj_intro diagnostic
    (public_claim -> False) hdiagnostic blocks

theorem ay_mpae_no_claim_diagnostic_reason
    (diagnostic : Prop) (public_claim : Prop) :
    AyMPAENoClaimDiagnostic diagnostic public_claim ->
    diagnostic := by
  intro diag
  exact ay_mpae_conj_left diagnostic (public_claim -> False) diag

theorem ay_mpae_no_claim_diagnostic_blocks
    (diagnostic : Prop) (public_claim : Prop) :
    AyMPAENoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  exact ay_mpae_conj_right diagnostic (public_claim -> False) diag

theorem ay_mpae_recompute_obligation_intro
    (reason : Prop) (recompute_request : Prop) :
    reason ->
    recompute_request ->
    AyMPAERecomputeObligation reason recompute_request := by
  intro hreason
  intro hrequest
  exact ay_mpae_conj_intro reason recompute_request hreason hrequest

theorem ay_mpae_incomplete_assignment_recompute
    (incomplete_assignment : Prop) (recompute_request : Prop) :
    incomplete_assignment ->
    recompute_request ->
    AyMPAERecomputeObligation
      incomplete_assignment recompute_request := by
  intro hincomplete
  intro hrequest
  exact ay_mpae_recompute_obligation_intro
    incomplete_assignment recompute_request hincomplete hrequest

theorem ay_mpae_incomplete_assignment_no_claim
    (incomplete_assignment : Prop) (public_claim : Prop) :
    incomplete_assignment ->
    (public_claim -> incomplete_assignment -> False) ->
    AyMPAENoClaimDiagnostic incomplete_assignment public_claim := by
  intro hincomplete
  intro blocks
  exact ay_mpae_no_claim_diagnostic_intro
    incomplete_assignment public_claim hincomplete
    (fun claim => blocks claim hincomplete)

theorem ay_mpae_frame_mismatch_no_claim
    (frame_mismatch : Prop) (public_claim : Prop) :
    frame_mismatch ->
    (public_claim -> frame_mismatch -> False) ->
    AyMPAENoClaimDiagnostic frame_mismatch public_claim := by
  intro hmismatch
  intro blocks
  exact ay_mpae_no_claim_diagnostic_intro
    frame_mismatch public_claim hmismatch
    (fun claim => blocks claim hmismatch)

theorem ay_mpae_extension_mismatch_no_claim
    (extension_mismatch : Prop) (public_claim : Prop) :
    extension_mismatch ->
    (public_claim -> extension_mismatch -> False) ->
    AyMPAENoClaimDiagnostic extension_mismatch public_claim := by
  intro hmismatch
  intro blocks
  exact ay_mpae_no_claim_diagnostic_intro
    extension_mismatch public_claim hmismatch
    (fun claim => blocks claim hmismatch)

theorem ay_mpae_diagnostic_blocks_public_claim
    (diagnostic : Prop) (public_claim : Prop) :
    AyMPAENoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  intro claim
  exact ay_mpae_no_claim_diagnostic_blocks
    diagnostic public_claim diag claim

theorem ay_mpae_bad_partial_no_stale_sat
    (incomplete_assignment : Prop) (frame_mismatch : Prop)
    (extension_mismatch : Prop) (public_claim : Prop) :
    (public_claim -> incomplete_assignment -> False) ->
    (public_claim -> frame_mismatch -> False) ->
    (public_claim -> extension_mismatch -> False) ->
    AyMPAEConj
      (incomplete_assignment ->
        AyMPAENoClaimDiagnostic incomplete_assignment public_claim)
      (AyMPAEConj
        (frame_mismatch ->
          AyMPAENoClaimDiagnostic frame_mismatch public_claim)
        (extension_mismatch ->
          AyMPAENoClaimDiagnostic extension_mismatch public_claim)) := by
  intro incomplete_blocks
  intro frame_blocks
  intro extension_blocks
  exact ay_mpae_conj_intro
    (incomplete_assignment ->
      AyMPAENoClaimDiagnostic incomplete_assignment public_claim)
    (AyMPAEConj
      (frame_mismatch ->
        AyMPAENoClaimDiagnostic frame_mismatch public_claim)
      (extension_mismatch ->
        AyMPAENoClaimDiagnostic extension_mismatch public_claim))
    (fun hincomplete =>
      ay_mpae_incomplete_assignment_no_claim
        incomplete_assignment public_claim hincomplete incomplete_blocks)
    (ay_mpae_conj_intro
      (frame_mismatch ->
        AyMPAENoClaimDiagnostic frame_mismatch public_claim)
      (extension_mismatch ->
        AyMPAENoClaimDiagnostic extension_mismatch public_claim)
      (fun hmismatch =>
        ay_mpae_frame_mismatch_no_claim
          frame_mismatch public_claim hmismatch frame_blocks)
      (fun hmismatch =>
        ay_mpae_extension_mismatch_no_claim
          extension_mismatch public_claim hmismatch extension_blocks))

def AyMPAEEliminatedVariableReconstruction
    (eliminated_domain : Prop) (reconstruction_map : Prop)
    (eliminated_values : Prop) :=
  AyMPAEConj eliminated_domain
    (AyMPAEConj reconstruction_map eliminated_values)

def AyMPAEFrameCompatibility
    (cube_frame : Prop) (assumption_frame : Prop)
    (refinement_frame : Prop) :=
  AyMPAEConj cube_frame
    (AyMPAEConj assumption_frame refinement_frame)

def AyMPAEFormulaFingerprintAgreement
    (simplified_fingerprint : Prop) (original_fingerprint : Prop)
    (fingerprint_match : Prop) :=
  AyMPAEConj simplified_fingerprint
    (AyMPAEConj original_fingerprint fingerprint_match)

def AyMPAEModelCheckerReplay
    (checker_accepts : Prop) (replay_trace : Prop) :=
  AyMPAEConj checker_accepts replay_trace

def AyMPAEPublicExtensionEvidence
    (extension_witness_ok : Prop) (eliminated_ok : Prop)
    (frame_ok : Prop) (fingerprint_ok : Prop)
    (checker_replay_ok : Prop) :=
  AyMPAEConj extension_witness_ok
    (AyMPAEConj eliminated_ok
      (AyMPAEConj frame_ok
        (AyMPAEConj fingerprint_ok checker_replay_ok)))

def AyMPAEPublicSatPublication
    (extension_evidence : Prop) (audit_entry : Prop)
    (public_sat_model : Prop) :=
  AyMPAEConj extension_evidence
    (AyMPAEConj audit_entry public_sat_model)

theorem ay_mpae_eliminated_reconstruction_intro
    (eliminated_domain : Prop) (reconstruction_map : Prop)
    (eliminated_values : Prop) :
    eliminated_domain ->
    reconstruction_map ->
    eliminated_values ->
    AyMPAEEliminatedVariableReconstruction
      eliminated_domain reconstruction_map eliminated_values := by
  intro hdomain
  intro hmap
  intro hvalues
  exact ay_mpae_conj_intro eliminated_domain
    (AyMPAEConj reconstruction_map eliminated_values)
    hdomain
    (ay_mpae_conj_intro reconstruction_map eliminated_values hmap hvalues)

theorem ay_mpae_eliminated_reconstruction_domain
    (eliminated_domain : Prop) (reconstruction_map : Prop)
    (eliminated_values : Prop) :
    AyMPAEEliminatedVariableReconstruction
      eliminated_domain reconstruction_map eliminated_values ->
    eliminated_domain := by
  intro evidence
  exact ay_mpae_conj_left eliminated_domain
    (AyMPAEConj reconstruction_map eliminated_values) evidence

theorem ay_mpae_eliminated_reconstruction_map
    (eliminated_domain : Prop) (reconstruction_map : Prop)
    (eliminated_values : Prop) :
    AyMPAEEliminatedVariableReconstruction
      eliminated_domain reconstruction_map eliminated_values ->
    reconstruction_map := by
  intro evidence
  exact ay_mpae_conj_left reconstruction_map eliminated_values
    (ay_mpae_conj_right eliminated_domain
      (AyMPAEConj reconstruction_map eliminated_values) evidence)

theorem ay_mpae_eliminated_reconstruction_values
    (eliminated_domain : Prop) (reconstruction_map : Prop)
    (eliminated_values : Prop) :
    AyMPAEEliminatedVariableReconstruction
      eliminated_domain reconstruction_map eliminated_values ->
    eliminated_values := by
  intro evidence
  exact ay_mpae_conj_right reconstruction_map eliminated_values
    (ay_mpae_conj_right eliminated_domain
      (AyMPAEConj reconstruction_map eliminated_values) evidence)

theorem ay_mpae_frame_compatibility_intro
    (cube_frame : Prop) (assumption_frame : Prop)
    (refinement_frame : Prop) :
    cube_frame ->
    assumption_frame ->
    refinement_frame ->
    AyMPAEFrameCompatibility
      cube_frame assumption_frame refinement_frame := by
  intro hcube
  intro hassumption
  intro hrefinement
  exact ay_mpae_conj_intro cube_frame
    (AyMPAEConj assumption_frame refinement_frame)
    hcube
    (ay_mpae_conj_intro assumption_frame refinement_frame
      hassumption hrefinement)

theorem ay_mpae_frame_compatibility_cube
    (cube_frame : Prop) (assumption_frame : Prop)
    (refinement_frame : Prop) :
    AyMPAEFrameCompatibility
      cube_frame assumption_frame refinement_frame ->
    cube_frame := by
  intro frame
  exact ay_mpae_conj_left cube_frame
    (AyMPAEConj assumption_frame refinement_frame) frame

theorem ay_mpae_frame_compatibility_assumption
    (cube_frame : Prop) (assumption_frame : Prop)
    (refinement_frame : Prop) :
    AyMPAEFrameCompatibility
      cube_frame assumption_frame refinement_frame ->
    assumption_frame := by
  intro frame
  exact ay_mpae_conj_left assumption_frame refinement_frame
    (ay_mpae_conj_right cube_frame
      (AyMPAEConj assumption_frame refinement_frame) frame)

theorem ay_mpae_frame_compatibility_refinement
    (cube_frame : Prop) (assumption_frame : Prop)
    (refinement_frame : Prop) :
    AyMPAEFrameCompatibility
      cube_frame assumption_frame refinement_frame ->
    refinement_frame := by
  intro frame
  exact ay_mpae_conj_right assumption_frame refinement_frame
    (ay_mpae_conj_right cube_frame
      (AyMPAEConj assumption_frame refinement_frame) frame)

theorem ay_mpae_formula_fingerprint_agreement_intro
    (simplified_fingerprint : Prop) (original_fingerprint : Prop)
    (fingerprint_match : Prop) :
    simplified_fingerprint ->
    original_fingerprint ->
    fingerprint_match ->
    AyMPAEFormulaFingerprintAgreement
      simplified_fingerprint original_fingerprint fingerprint_match := by
  intro hsimplified
  intro horiginal
  intro hmatch
  exact ay_mpae_conj_intro simplified_fingerprint
    (AyMPAEConj original_fingerprint fingerprint_match)
    hsimplified
    (ay_mpae_conj_intro original_fingerprint fingerprint_match
      horiginal hmatch)

theorem ay_mpae_formula_fingerprint_agreement_simplified
    (simplified_fingerprint : Prop) (original_fingerprint : Prop)
    (fingerprint_match : Prop) :
    AyMPAEFormulaFingerprintAgreement
      simplified_fingerprint original_fingerprint fingerprint_match ->
    simplified_fingerprint := by
  intro fp
  exact ay_mpae_conj_left simplified_fingerprint
    (AyMPAEConj original_fingerprint fingerprint_match) fp

theorem ay_mpae_formula_fingerprint_agreement_original
    (simplified_fingerprint : Prop) (original_fingerprint : Prop)
    (fingerprint_match : Prop) :
    AyMPAEFormulaFingerprintAgreement
      simplified_fingerprint original_fingerprint fingerprint_match ->
    original_fingerprint := by
  intro fp
  exact ay_mpae_conj_left original_fingerprint fingerprint_match
    (ay_mpae_conj_right simplified_fingerprint
      (AyMPAEConj original_fingerprint fingerprint_match) fp)

theorem ay_mpae_formula_fingerprint_agreement_match
    (simplified_fingerprint : Prop) (original_fingerprint : Prop)
    (fingerprint_match : Prop) :
    AyMPAEFormulaFingerprintAgreement
      simplified_fingerprint original_fingerprint fingerprint_match ->
    fingerprint_match := by
  intro fp
  exact ay_mpae_conj_right original_fingerprint fingerprint_match
    (ay_mpae_conj_right simplified_fingerprint
      (AyMPAEConj original_fingerprint fingerprint_match) fp)

theorem ay_mpae_model_checker_replay_intro
    (checker_accepts : Prop) (replay_trace : Prop) :
    checker_accepts ->
    replay_trace ->
    AyMPAEModelCheckerReplay checker_accepts replay_trace := by
  intro haccepts
  intro htrace
  exact ay_mpae_conj_intro checker_accepts replay_trace haccepts htrace

theorem ay_mpae_model_checker_replay_accepts
    (checker_accepts : Prop) (replay_trace : Prop) :
    AyMPAEModelCheckerReplay checker_accepts replay_trace ->
    checker_accepts := by
  intro replay
  exact ay_mpae_conj_left checker_accepts replay_trace replay

theorem ay_mpae_model_checker_replay_trace
    (checker_accepts : Prop) (replay_trace : Prop) :
    AyMPAEModelCheckerReplay checker_accepts replay_trace ->
    replay_trace := by
  intro replay
  exact ay_mpae_conj_right checker_accepts replay_trace replay

theorem ay_mpae_public_extension_evidence_intro
    (extension_witness_ok : Prop) (eliminated_ok : Prop)
    (frame_ok : Prop) (fingerprint_ok : Prop)
    (checker_replay_ok : Prop) :
    extension_witness_ok ->
    eliminated_ok ->
    frame_ok ->
    fingerprint_ok ->
    checker_replay_ok ->
    AyMPAEPublicExtensionEvidence
      extension_witness_ok eliminated_ok frame_ok fingerprint_ok
      checker_replay_ok := by
  intro hextension
  intro heliminated
  intro hframe
  intro hfingerprint
  intro hchecker
  exact ay_mpae_conj_intro extension_witness_ok
    (AyMPAEConj eliminated_ok
      (AyMPAEConj frame_ok
        (AyMPAEConj fingerprint_ok checker_replay_ok)))
    hextension
    (ay_mpae_conj_intro eliminated_ok
      (AyMPAEConj frame_ok
        (AyMPAEConj fingerprint_ok checker_replay_ok))
      heliminated
      (ay_mpae_conj_intro frame_ok
        (AyMPAEConj fingerprint_ok checker_replay_ok)
        hframe
        (ay_mpae_conj_intro fingerprint_ok checker_replay_ok
          hfingerprint hchecker)))

theorem ay_mpae_public_extension_evidence_extension
    (extension_witness_ok : Prop) (eliminated_ok : Prop)
    (frame_ok : Prop) (fingerprint_ok : Prop)
    (checker_replay_ok : Prop) :
    AyMPAEPublicExtensionEvidence
      extension_witness_ok eliminated_ok frame_ok fingerprint_ok
      checker_replay_ok ->
    extension_witness_ok := by
  intro evidence
  exact ay_mpae_conj_left extension_witness_ok
    (AyMPAEConj eliminated_ok
      (AyMPAEConj frame_ok
        (AyMPAEConj fingerprint_ok checker_replay_ok))) evidence

theorem ay_mpae_public_extension_evidence_eliminated
    (extension_witness_ok : Prop) (eliminated_ok : Prop)
    (frame_ok : Prop) (fingerprint_ok : Prop)
    (checker_replay_ok : Prop) :
    AyMPAEPublicExtensionEvidence
      extension_witness_ok eliminated_ok frame_ok fingerprint_ok
      checker_replay_ok ->
    eliminated_ok := by
  intro evidence
  exact ay_mpae_conj_left eliminated_ok
    (AyMPAEConj frame_ok
      (AyMPAEConj fingerprint_ok checker_replay_ok))
    (ay_mpae_conj_right extension_witness_ok
      (AyMPAEConj eliminated_ok
        (AyMPAEConj frame_ok
          (AyMPAEConj fingerprint_ok checker_replay_ok))) evidence)

theorem ay_mpae_public_extension_evidence_frame
    (extension_witness_ok : Prop) (eliminated_ok : Prop)
    (frame_ok : Prop) (fingerprint_ok : Prop)
    (checker_replay_ok : Prop) :
    AyMPAEPublicExtensionEvidence
      extension_witness_ok eliminated_ok frame_ok fingerprint_ok
      checker_replay_ok ->
    frame_ok := by
  intro evidence
  exact ay_mpae_conj_left frame_ok
    (AyMPAEConj fingerprint_ok checker_replay_ok)
    (ay_mpae_conj_right eliminated_ok
      (AyMPAEConj frame_ok
        (AyMPAEConj fingerprint_ok checker_replay_ok))
      (ay_mpae_conj_right extension_witness_ok
        (AyMPAEConj eliminated_ok
          (AyMPAEConj frame_ok
            (AyMPAEConj fingerprint_ok checker_replay_ok))) evidence))

theorem ay_mpae_public_extension_evidence_fingerprint
    (extension_witness_ok : Prop) (eliminated_ok : Prop)
    (frame_ok : Prop) (fingerprint_ok : Prop)
    (checker_replay_ok : Prop) :
    AyMPAEPublicExtensionEvidence
      extension_witness_ok eliminated_ok frame_ok fingerprint_ok
      checker_replay_ok ->
    fingerprint_ok := by
  intro evidence
  exact ay_mpae_conj_left fingerprint_ok checker_replay_ok
    (ay_mpae_conj_right frame_ok
      (AyMPAEConj fingerprint_ok checker_replay_ok)
      (ay_mpae_conj_right eliminated_ok
        (AyMPAEConj frame_ok
          (AyMPAEConj fingerprint_ok checker_replay_ok))
        (ay_mpae_conj_right extension_witness_ok
          (AyMPAEConj eliminated_ok
            (AyMPAEConj frame_ok
              (AyMPAEConj fingerprint_ok checker_replay_ok))) evidence)))

theorem ay_mpae_public_extension_evidence_checker
    (extension_witness_ok : Prop) (eliminated_ok : Prop)
    (frame_ok : Prop) (fingerprint_ok : Prop)
    (checker_replay_ok : Prop) :
    AyMPAEPublicExtensionEvidence
      extension_witness_ok eliminated_ok frame_ok fingerprint_ok
      checker_replay_ok ->
    checker_replay_ok := by
  intro evidence
  exact ay_mpae_conj_right fingerprint_ok checker_replay_ok
    (ay_mpae_conj_right frame_ok
      (AyMPAEConj fingerprint_ok checker_replay_ok)
      (ay_mpae_conj_right eliminated_ok
        (AyMPAEConj frame_ok
          (AyMPAEConj fingerprint_ok checker_replay_ok))
        (ay_mpae_conj_right extension_witness_ok
          (AyMPAEConj eliminated_ok
            (AyMPAEConj frame_ok
              (AyMPAEConj fingerprint_ok checker_replay_ok))) evidence)))

theorem ay_mpae_public_sat_publication_intro
    (extension_evidence : Prop) (audit_entry : Prop)
    (public_sat_model : Prop) :
    extension_evidence ->
    audit_entry ->
    public_sat_model ->
    AyMPAEPublicSatPublication
      extension_evidence audit_entry public_sat_model := by
  intro hevidence
  intro haudit
  intro hmodel
  exact ay_mpae_conj_intro extension_evidence
    (AyMPAEConj audit_entry public_sat_model)
    hevidence
    (ay_mpae_conj_intro audit_entry public_sat_model haudit hmodel)

theorem ay_mpae_public_sat_publication_evidence
    (extension_evidence : Prop) (audit_entry : Prop)
    (public_sat_model : Prop) :
    AyMPAEPublicSatPublication
      extension_evidence audit_entry public_sat_model ->
    extension_evidence := by
  intro publication
  exact ay_mpae_conj_left extension_evidence
    (AyMPAEConj audit_entry public_sat_model) publication

theorem ay_mpae_public_sat_publication_audit
    (extension_evidence : Prop) (audit_entry : Prop)
    (public_sat_model : Prop) :
    AyMPAEPublicSatPublication
      extension_evidence audit_entry public_sat_model ->
    audit_entry := by
  intro publication
  exact ay_mpae_conj_left audit_entry public_sat_model
    (ay_mpae_conj_right extension_evidence
      (AyMPAEConj audit_entry public_sat_model) publication)

theorem ay_mpae_public_sat_publication_model
    (extension_evidence : Prop) (audit_entry : Prop)
    (public_sat_model : Prop) :
    AyMPAEPublicSatPublication
      extension_evidence audit_entry public_sat_model ->
    public_sat_model := by
  intro publication
  exact ay_mpae_conj_right audit_entry public_sat_model
    (ay_mpae_conj_right extension_evidence
      (AyMPAEConj audit_entry public_sat_model) publication)

theorem ay_mpae_accepted_extension_preserves_sat_publication
    (extension_evidence : Prop) (audit_entry : Prop)
    (public_sat_model : Prop) :
    AyMPAEPublicSatPublication
      extension_evidence audit_entry public_sat_model ->
    public_sat_model := by
  intro publication
  exact ay_mpae_public_sat_publication_model
    extension_evidence audit_entry public_sat_model publication

theorem ay_mpae_public_extension_report_from_witness
    (partial_assignment : Prop) (full_assignment : Prop)
    (public_sat_model : Prop) (extension_witness_ok : Prop)
    (eliminated_ok : Prop) (frame_ok : Prop)
    (fingerprint_ok : Prop) (checker_replay_ok : Prop)
    (audit_entry : Prop) :
    AyMPAEExtensionWitness partial_assignment full_assignment ->
    AyMPAEFormulaReconstruction full_assignment public_sat_model ->
    partial_assignment ->
    extension_witness_ok ->
    eliminated_ok ->
    frame_ok ->
    fingerprint_ok ->
    checker_replay_ok ->
    audit_entry ->
    AyMPAEPublicSatPublication
      (AyMPAEPublicExtensionEvidence
        extension_witness_ok eliminated_ok frame_ok fingerprint_ok
        checker_replay_ok)
      audit_entry public_sat_model := by
  intro extend
  intro reconstruct
  intro hpartial
  intro hextension
  intro heliminated
  intro hframe
  intro hfingerprint
  intro hchecker
  intro haudit
  exact ay_mpae_public_sat_publication_intro
    (AyMPAEPublicExtensionEvidence
      extension_witness_ok eliminated_ok frame_ok fingerprint_ok
      checker_replay_ok)
    audit_entry public_sat_model
    (ay_mpae_public_extension_evidence_intro
      extension_witness_ok eliminated_ok frame_ok fingerprint_ok
      checker_replay_ok hextension heliminated hframe hfingerprint hchecker)
    haudit
    (reconstruct (extend hpartial))

theorem ay_mpae_publication_requires_extension_witness
    (extension_witness_ok : Prop) (eliminated_ok : Prop)
    (frame_ok : Prop) (fingerprint_ok : Prop)
    (checker_replay_ok : Prop) (audit_entry : Prop)
    (public_sat_model : Prop) :
    AyMPAEPublicSatPublication
      (AyMPAEPublicExtensionEvidence
        extension_witness_ok eliminated_ok frame_ok fingerprint_ok
        checker_replay_ok)
      audit_entry public_sat_model ->
    extension_witness_ok := by
  intro publication
  exact ay_mpae_public_extension_evidence_extension
    extension_witness_ok eliminated_ok frame_ok fingerprint_ok checker_replay_ok
    (ay_mpae_public_sat_publication_evidence
      (AyMPAEPublicExtensionEvidence
        extension_witness_ok eliminated_ok frame_ok fingerprint_ok
        checker_replay_ok)
      audit_entry public_sat_model publication)

theorem ay_mpae_publication_requires_eliminated_reconstruction
    (extension_witness_ok : Prop) (eliminated_ok : Prop)
    (frame_ok : Prop) (fingerprint_ok : Prop)
    (checker_replay_ok : Prop) (audit_entry : Prop)
    (public_sat_model : Prop) :
    AyMPAEPublicSatPublication
      (AyMPAEPublicExtensionEvidence
        extension_witness_ok eliminated_ok frame_ok fingerprint_ok
        checker_replay_ok)
      audit_entry public_sat_model ->
    eliminated_ok := by
  intro publication
  exact ay_mpae_public_extension_evidence_eliminated
    extension_witness_ok eliminated_ok frame_ok fingerprint_ok checker_replay_ok
    (ay_mpae_public_sat_publication_evidence
      (AyMPAEPublicExtensionEvidence
        extension_witness_ok eliminated_ok frame_ok fingerprint_ok
        checker_replay_ok)
      audit_entry public_sat_model publication)

theorem ay_mpae_publication_requires_frame_compatibility
    (extension_witness_ok : Prop) (eliminated_ok : Prop)
    (frame_ok : Prop) (fingerprint_ok : Prop)
    (checker_replay_ok : Prop) (audit_entry : Prop)
    (public_sat_model : Prop) :
    AyMPAEPublicSatPublication
      (AyMPAEPublicExtensionEvidence
        extension_witness_ok eliminated_ok frame_ok fingerprint_ok
        checker_replay_ok)
      audit_entry public_sat_model ->
    frame_ok := by
  intro publication
  exact ay_mpae_public_extension_evidence_frame
    extension_witness_ok eliminated_ok frame_ok fingerprint_ok checker_replay_ok
    (ay_mpae_public_sat_publication_evidence
      (AyMPAEPublicExtensionEvidence
        extension_witness_ok eliminated_ok frame_ok fingerprint_ok
        checker_replay_ok)
      audit_entry public_sat_model publication)

theorem ay_mpae_publication_requires_fingerprint
    (extension_witness_ok : Prop) (eliminated_ok : Prop)
    (frame_ok : Prop) (fingerprint_ok : Prop)
    (checker_replay_ok : Prop) (audit_entry : Prop)
    (public_sat_model : Prop) :
    AyMPAEPublicSatPublication
      (AyMPAEPublicExtensionEvidence
        extension_witness_ok eliminated_ok frame_ok fingerprint_ok
        checker_replay_ok)
      audit_entry public_sat_model ->
    fingerprint_ok := by
  intro publication
  exact ay_mpae_public_extension_evidence_fingerprint
    extension_witness_ok eliminated_ok frame_ok fingerprint_ok checker_replay_ok
    (ay_mpae_public_sat_publication_evidence
      (AyMPAEPublicExtensionEvidence
        extension_witness_ok eliminated_ok frame_ok fingerprint_ok
        checker_replay_ok)
      audit_entry public_sat_model publication)

theorem ay_mpae_publication_requires_checker_replay
    (extension_witness_ok : Prop) (eliminated_ok : Prop)
    (frame_ok : Prop) (fingerprint_ok : Prop)
    (checker_replay_ok : Prop) (audit_entry : Prop)
    (public_sat_model : Prop) :
    AyMPAEPublicSatPublication
      (AyMPAEPublicExtensionEvidence
        extension_witness_ok eliminated_ok frame_ok fingerprint_ok
        checker_replay_ok)
      audit_entry public_sat_model ->
    checker_replay_ok := by
  intro publication
  exact ay_mpae_public_extension_evidence_checker
    extension_witness_ok eliminated_ok frame_ok fingerprint_ok checker_replay_ok
    (ay_mpae_public_sat_publication_evidence
      (AyMPAEPublicExtensionEvidence
        extension_witness_ok eliminated_ok frame_ok fingerprint_ok
        checker_replay_ok)
      audit_entry public_sat_model publication)

theorem ay_mpae_missing_extension_witness_recompute
    (missing_extension_witness : Prop) (recompute_request : Prop) :
    missing_extension_witness ->
    recompute_request ->
    AyMPAERecomputeObligation
      missing_extension_witness recompute_request := by
  intro hmissing
  intro hrequest
  exact ay_mpae_recompute_obligation_intro
    missing_extension_witness recompute_request hmissing hrequest

theorem ay_mpae_missing_extension_witness_no_claim
    (missing_extension_witness : Prop) (public_claim : Prop) :
    missing_extension_witness ->
    (public_claim -> missing_extension_witness -> False) ->
    AyMPAENoClaimDiagnostic missing_extension_witness public_claim := by
  intro hmissing
  intro blocks
  exact ay_mpae_no_claim_diagnostic_intro
    missing_extension_witness public_claim hmissing
    (fun claim => blocks claim hmissing)

theorem ay_mpae_stale_fingerprint_no_claim
    (stale_fingerprint : Prop) (public_claim : Prop) :
    stale_fingerprint ->
    (public_claim -> stale_fingerprint -> False) ->
    AyMPAENoClaimDiagnostic stale_fingerprint public_claim := by
  intro hstale
  intro blocks
  exact ay_mpae_no_claim_diagnostic_intro
    stale_fingerprint public_claim hstale
    (fun claim => blocks claim hstale)

theorem ay_mpae_eliminated_variable_mismatch_no_claim
    (eliminated_variable_mismatch : Prop) (public_claim : Prop) :
    eliminated_variable_mismatch ->
    (public_claim -> eliminated_variable_mismatch -> False) ->
    AyMPAENoClaimDiagnostic eliminated_variable_mismatch public_claim := by
  intro hmismatch
  intro blocks
  exact ay_mpae_no_claim_diagnostic_intro
    eliminated_variable_mismatch public_claim hmismatch
    (fun claim => blocks claim hmismatch)

theorem ay_mpae_checker_rejection_no_claim
    (checker_rejection : Prop) (public_claim : Prop) :
    checker_rejection ->
    (public_claim -> checker_rejection -> False) ->
    AyMPAENoClaimDiagnostic checker_rejection public_claim := by
  intro hreject
  intro blocks
  exact ay_mpae_no_claim_diagnostic_intro
    checker_rejection public_claim hreject
    (fun claim => blocks claim hreject)

theorem ay_mpae_bad_extension_no_stale_sat_publication
    (missing_extension_witness : Prop) (stale_frame : Prop)
    (stale_fingerprint : Prop) (eliminated_variable_mismatch : Prop)
    (checker_rejection : Prop) (public_claim : Prop) :
    (public_claim -> missing_extension_witness -> False) ->
    (public_claim -> stale_frame -> False) ->
    (public_claim -> stale_fingerprint -> False) ->
    (public_claim -> eliminated_variable_mismatch -> False) ->
    (public_claim -> checker_rejection -> False) ->
    AyMPAEConj
      (missing_extension_witness ->
        AyMPAENoClaimDiagnostic missing_extension_witness public_claim)
      (AyMPAEConj
        (stale_frame ->
          AyMPAENoClaimDiagnostic stale_frame public_claim)
        (AyMPAEConj
          (stale_fingerprint ->
            AyMPAENoClaimDiagnostic stale_fingerprint public_claim)
          (AyMPAEConj
            (eliminated_variable_mismatch ->
              AyMPAENoClaimDiagnostic
                eliminated_variable_mismatch public_claim)
            (checker_rejection ->
              AyMPAENoClaimDiagnostic checker_rejection public_claim)))) := by
  intro missing_blocks
  intro frame_blocks
  intro fingerprint_blocks
  intro eliminated_blocks
  intro checker_blocks
  exact ay_mpae_conj_intro
    (missing_extension_witness ->
      AyMPAENoClaimDiagnostic missing_extension_witness public_claim)
    (AyMPAEConj
      (stale_frame ->
        AyMPAENoClaimDiagnostic stale_frame public_claim)
      (AyMPAEConj
        (stale_fingerprint ->
          AyMPAENoClaimDiagnostic stale_fingerprint public_claim)
        (AyMPAEConj
          (eliminated_variable_mismatch ->
            AyMPAENoClaimDiagnostic
              eliminated_variable_mismatch public_claim)
          (checker_rejection ->
            AyMPAENoClaimDiagnostic checker_rejection public_claim))))
    (fun hmissing =>
      ay_mpae_missing_extension_witness_no_claim
        missing_extension_witness public_claim hmissing missing_blocks)
    (ay_mpae_conj_intro
      (stale_frame ->
        AyMPAENoClaimDiagnostic stale_frame public_claim)
      (AyMPAEConj
        (stale_fingerprint ->
          AyMPAENoClaimDiagnostic stale_fingerprint public_claim)
        (AyMPAEConj
          (eliminated_variable_mismatch ->
            AyMPAENoClaimDiagnostic
              eliminated_variable_mismatch public_claim)
          (checker_rejection ->
            AyMPAENoClaimDiagnostic checker_rejection public_claim)))
      (fun hframe =>
        ay_mpae_frame_mismatch_no_claim
          stale_frame public_claim hframe frame_blocks)
      (ay_mpae_conj_intro
        (stale_fingerprint ->
          AyMPAENoClaimDiagnostic stale_fingerprint public_claim)
        (AyMPAEConj
          (eliminated_variable_mismatch ->
            AyMPAENoClaimDiagnostic
              eliminated_variable_mismatch public_claim)
          (checker_rejection ->
            AyMPAENoClaimDiagnostic checker_rejection public_claim))
        (fun hstale =>
          ay_mpae_stale_fingerprint_no_claim
            stale_fingerprint public_claim hstale fingerprint_blocks)
        (ay_mpae_conj_intro
          (eliminated_variable_mismatch ->
            AyMPAENoClaimDiagnostic
              eliminated_variable_mismatch public_claim)
          (checker_rejection ->
            AyMPAENoClaimDiagnostic checker_rejection public_claim)
          (fun hmismatch =>
            ay_mpae_eliminated_variable_mismatch_no_claim
              eliminated_variable_mismatch public_claim
              hmismatch eliminated_blocks)
          (fun hreject =>
            ay_mpae_checker_rejection_no_claim
              checker_rejection public_claim hreject checker_blocks))))
