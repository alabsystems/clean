-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked SAT-specific skeleton for cube-cover SAT candidate soundness.
-- Cube/assumption partition search may publish SAT candidates only when cube
-- membership, frame identity, partial assignment extension, formula
-- reconstruction, and model checker evidence all agree. Bad cube evidence is
-- diagnostic no-claim/recompute data.

def AyMCCCConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyMCCCDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyMCCCEquisat (before : Prop) (after : Prop) :=
  AyMCCCConj (before -> after) (after -> before)

def AyMCCCCubeMembership
    (cube_id : Prop) (cover_membership : Prop) :=
  AyMCCCConj cube_id cover_membership

def AyMCCCAssumptionFrameIdentity
    (cube_frame : Prop) (solver_frame : Prop) :=
  AyMCCCConj cube_frame solver_frame

def AyMCCCPartialCandidate
    (partial_assignment : Prop) (cube_assignment : Prop) :=
  AyMCCCConj partial_assignment cube_assignment

def AyMCCCExtensionWitness
    (partial_candidate : Prop) (full_assignment : Prop) :=
  partial_candidate -> full_assignment

def AyMCCCFormulaReconstruction
    (full_assignment : Prop) (original_model : Prop) :=
  full_assignment -> original_model

def AyMCCCCandidateEvidence
    (membership_ok : Prop) (frame_ok : Prop)
    (extension_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :=
  AyMCCCConj membership_ok
    (AyMCCCConj frame_ok
      (AyMCCCConj extension_ok
        (AyMCCCConj reconstruction_ok checker_ok)))

def AyMCCCAcceptedSatCandidate
    (candidate_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :=
  AyMCCCConj candidate_evidence
    (AyMCCCConj audit_entry original_model)

def AyMCCCNoClaimDiagnostic
    (diagnostic : Prop) (public_claim : Prop) :=
  AyMCCCConj diagnostic (public_claim -> False)

def AyMCCCRecomputeObligation
    (reason : Prop) (recompute_request : Prop) :=
  AyMCCCConj reason recompute_request

theorem ay_mccc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyMCCCConj left right := by
  intro hleft
  intro hright
  intro result
  intro build
  exact build hleft hright

theorem ay_mccc_conj_left
    (left : Prop) (right : Prop) :
    AyMCCCConj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_mccc_conj_right
    (left : Prop) (right : Prop) :
    AyMCCCConj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_mccc_disj_left
    (left : Prop) (right : Prop) :
    left -> AyMCCCDisj left right := by
  intro hleft
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hleft

theorem ay_mccc_disj_right
    (left : Prop) (right : Prop) :
    right -> AyMCCCDisj left right := by
  intro hright
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hright

theorem ay_mccc_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyMCCCEquisat before after := by
  intro forward
  intro backward
  exact ay_mccc_conj_intro
    (before -> after) (after -> before) forward backward

theorem ay_mccc_equisat_forward
    (before : Prop) (after : Prop) :
    AyMCCCEquisat before after -> before -> after := by
  intro certificate
  exact ay_mccc_conj_left (before -> after) (after -> before) certificate

theorem ay_mccc_equisat_backward
    (before : Prop) (after : Prop) :
    AyMCCCEquisat before after -> after -> before := by
  intro certificate
  exact ay_mccc_conj_right (before -> after) (after -> before) certificate

theorem ay_mccc_cube_membership_intro
    (cube_id : Prop) (cover_membership : Prop) :
    cube_id ->
    cover_membership ->
    AyMCCCCubeMembership cube_id cover_membership := by
  intro hcube
  intro hmembership
  exact ay_mccc_conj_intro cube_id cover_membership
    hcube hmembership

theorem ay_mccc_cube_membership_cube
    (cube_id : Prop) (cover_membership : Prop) :
    AyMCCCCubeMembership cube_id cover_membership ->
    cube_id := by
  intro membership
  exact ay_mccc_conj_left cube_id cover_membership membership

theorem ay_mccc_cube_membership_cover
    (cube_id : Prop) (cover_membership : Prop) :
    AyMCCCCubeMembership cube_id cover_membership ->
    cover_membership := by
  intro membership
  exact ay_mccc_conj_right cube_id cover_membership membership

theorem ay_mccc_frame_identity_intro
    (cube_frame : Prop) (solver_frame : Prop) :
    cube_frame ->
    solver_frame ->
    AyMCCCAssumptionFrameIdentity cube_frame solver_frame := by
  intro hcube
  intro hsolver
  exact ay_mccc_conj_intro cube_frame solver_frame hcube hsolver

theorem ay_mccc_frame_identity_cube
    (cube_frame : Prop) (solver_frame : Prop) :
    AyMCCCAssumptionFrameIdentity cube_frame solver_frame ->
    cube_frame := by
  intro frame
  exact ay_mccc_conj_left cube_frame solver_frame frame

theorem ay_mccc_frame_identity_solver
    (cube_frame : Prop) (solver_frame : Prop) :
    AyMCCCAssumptionFrameIdentity cube_frame solver_frame ->
    solver_frame := by
  intro frame
  exact ay_mccc_conj_right cube_frame solver_frame frame

theorem ay_mccc_partial_candidate_intro
    (partial_assignment : Prop) (cube_assignment : Prop) :
    partial_assignment ->
    cube_assignment ->
    AyMCCCPartialCandidate partial_assignment cube_assignment := by
  intro hpartial
  intro hcube
  exact ay_mccc_conj_intro partial_assignment cube_assignment
    hpartial hcube

theorem ay_mccc_partial_candidate_partial
    (partial_assignment : Prop) (cube_assignment : Prop) :
    AyMCCCPartialCandidate partial_assignment cube_assignment ->
    partial_assignment := by
  intro candidate
  exact ay_mccc_conj_left partial_assignment cube_assignment candidate

theorem ay_mccc_partial_candidate_cube
    (partial_assignment : Prop) (cube_assignment : Prop) :
    AyMCCCPartialCandidate partial_assignment cube_assignment ->
    cube_assignment := by
  intro candidate
  exact ay_mccc_conj_right partial_assignment cube_assignment candidate

theorem ay_mccc_extension_apply
    (partial_candidate : Prop) (full_assignment : Prop) :
    AyMCCCExtensionWitness partial_candidate full_assignment ->
    partial_candidate ->
    full_assignment := by
  intro extend
  intro hpartial
  exact extend hpartial

theorem ay_mccc_reconstruct_apply
    (full_assignment : Prop) (original_model : Prop) :
    AyMCCCFormulaReconstruction full_assignment original_model ->
    full_assignment ->
    original_model := by
  intro reconstruct
  intro hfull
  exact reconstruct hfull

theorem ay_mccc_candidate_evidence_intro
    (membership_ok : Prop) (frame_ok : Prop)
    (extension_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :
    membership_ok ->
    frame_ok ->
    extension_ok ->
    reconstruction_ok ->
    checker_ok ->
    AyMCCCCandidateEvidence
      membership_ok frame_ok extension_ok reconstruction_ok checker_ok := by
  intro hmembership
  intro hframe
  intro hextension
  intro hreconstruction
  intro hchecker
  exact ay_mccc_conj_intro membership_ok
    (AyMCCCConj frame_ok
      (AyMCCCConj extension_ok
        (AyMCCCConj reconstruction_ok checker_ok)))
    hmembership
    (ay_mccc_conj_intro frame_ok
      (AyMCCCConj extension_ok
        (AyMCCCConj reconstruction_ok checker_ok))
      hframe
      (ay_mccc_conj_intro extension_ok
        (AyMCCCConj reconstruction_ok checker_ok)
        hextension
        (ay_mccc_conj_intro reconstruction_ok checker_ok
          hreconstruction hchecker)))

theorem ay_mccc_candidate_evidence_membership
    (membership_ok : Prop) (frame_ok : Prop)
    (extension_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :
    AyMCCCCandidateEvidence
      membership_ok frame_ok extension_ok reconstruction_ok checker_ok ->
    membership_ok := by
  intro evidence
  exact ay_mccc_conj_left membership_ok
    (AyMCCCConj frame_ok
      (AyMCCCConj extension_ok
        (AyMCCCConj reconstruction_ok checker_ok))) evidence

theorem ay_mccc_candidate_evidence_frame
    (membership_ok : Prop) (frame_ok : Prop)
    (extension_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :
    AyMCCCCandidateEvidence
      membership_ok frame_ok extension_ok reconstruction_ok checker_ok ->
    frame_ok := by
  intro evidence
  exact ay_mccc_conj_left frame_ok
    (AyMCCCConj extension_ok
      (AyMCCCConj reconstruction_ok checker_ok))
    (ay_mccc_conj_right membership_ok
      (AyMCCCConj frame_ok
        (AyMCCCConj extension_ok
          (AyMCCCConj reconstruction_ok checker_ok))) evidence)

theorem ay_mccc_candidate_evidence_extension
    (membership_ok : Prop) (frame_ok : Prop)
    (extension_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :
    AyMCCCCandidateEvidence
      membership_ok frame_ok extension_ok reconstruction_ok checker_ok ->
    extension_ok := by
  intro evidence
  exact ay_mccc_conj_left extension_ok
    (AyMCCCConj reconstruction_ok checker_ok)
    (ay_mccc_conj_right frame_ok
      (AyMCCCConj extension_ok
        (AyMCCCConj reconstruction_ok checker_ok))
      (ay_mccc_conj_right membership_ok
        (AyMCCCConj frame_ok
          (AyMCCCConj extension_ok
            (AyMCCCConj reconstruction_ok checker_ok))) evidence))

theorem ay_mccc_candidate_evidence_reconstruction
    (membership_ok : Prop) (frame_ok : Prop)
    (extension_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :
    AyMCCCCandidateEvidence
      membership_ok frame_ok extension_ok reconstruction_ok checker_ok ->
    reconstruction_ok := by
  intro evidence
  exact ay_mccc_conj_left reconstruction_ok checker_ok
    (ay_mccc_conj_right extension_ok
      (AyMCCCConj reconstruction_ok checker_ok)
      (ay_mccc_conj_right frame_ok
        (AyMCCCConj extension_ok
          (AyMCCCConj reconstruction_ok checker_ok))
        (ay_mccc_conj_right membership_ok
          (AyMCCCConj frame_ok
            (AyMCCCConj extension_ok
              (AyMCCCConj reconstruction_ok checker_ok))) evidence)))

theorem ay_mccc_candidate_evidence_checker
    (membership_ok : Prop) (frame_ok : Prop)
    (extension_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) :
    AyMCCCCandidateEvidence
      membership_ok frame_ok extension_ok reconstruction_ok checker_ok ->
    checker_ok := by
  intro evidence
  exact ay_mccc_conj_right reconstruction_ok checker_ok
    (ay_mccc_conj_right extension_ok
      (AyMCCCConj reconstruction_ok checker_ok)
      (ay_mccc_conj_right frame_ok
        (AyMCCCConj extension_ok
          (AyMCCCConj reconstruction_ok checker_ok))
        (ay_mccc_conj_right membership_ok
          (AyMCCCConj frame_ok
            (AyMCCCConj extension_ok
              (AyMCCCConj reconstruction_ok checker_ok))) evidence)))

theorem ay_mccc_report_intro
    (candidate_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    candidate_evidence ->
    audit_entry ->
    original_model ->
    AyMCCCAcceptedSatCandidate
      candidate_evidence audit_entry original_model := by
  intro hevidence
  intro haudit
  intro horiginal
  exact ay_mccc_conj_intro candidate_evidence
    (AyMCCCConj audit_entry original_model)
    hevidence
    (ay_mccc_conj_intro audit_entry original_model haudit horiginal)

theorem ay_mccc_report_evidence
    (candidate_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMCCCAcceptedSatCandidate
      candidate_evidence audit_entry original_model ->
    candidate_evidence := by
  intro report
  exact ay_mccc_conj_left candidate_evidence
    (AyMCCCConj audit_entry original_model) report

theorem ay_mccc_report_audit
    (candidate_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMCCCAcceptedSatCandidate
      candidate_evidence audit_entry original_model ->
    audit_entry := by
  intro report
  exact ay_mccc_conj_left audit_entry original_model
    (ay_mccc_conj_right candidate_evidence
      (AyMCCCConj audit_entry original_model) report)

theorem ay_mccc_report_original
    (candidate_evidence : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMCCCAcceptedSatCandidate
      candidate_evidence audit_entry original_model ->
    original_model := by
  intro report
  exact ay_mccc_conj_right audit_entry original_model
    (ay_mccc_conj_right candidate_evidence
      (AyMCCCConj audit_entry original_model) report)

theorem ay_mccc_extended_original_model
    (partial_candidate : Prop) (full_assignment : Prop)
    (original_model : Prop) :
    AyMCCCExtensionWitness partial_candidate full_assignment ->
    AyMCCCFormulaReconstruction full_assignment original_model ->
    partial_candidate ->
    original_model := by
  intro extend
  intro reconstruct
  intro hpartial
  exact reconstruct (extend hpartial)

theorem ay_mccc_candidate_report_from_evidence
    (partial_candidate : Prop) (full_assignment : Prop)
    (original_model : Prop) (membership_ok : Prop)
    (frame_ok : Prop) (extension_ok : Prop)
    (reconstruction_ok : Prop) (checker_ok : Prop)
    (audit_entry : Prop) :
    AyMCCCExtensionWitness partial_candidate full_assignment ->
    AyMCCCFormulaReconstruction full_assignment original_model ->
    partial_candidate ->
    membership_ok ->
    frame_ok ->
    extension_ok ->
    reconstruction_ok ->
    checker_ok ->
    audit_entry ->
    AyMCCCAcceptedSatCandidate
      (AyMCCCCandidateEvidence
        membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
      audit_entry original_model := by
  intro extend
  intro reconstruct
  intro hpartial
  intro hmembership
  intro hframe
  intro hextension
  intro hreconstruction
  intro hchecker
  intro haudit
  exact ay_mccc_report_intro
    (AyMCCCCandidateEvidence
      membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
    audit_entry original_model
    (ay_mccc_candidate_evidence_intro
      membership_ok frame_ok extension_ok reconstruction_ok checker_ok
      hmembership hframe hextension hreconstruction hchecker)
    haudit
    (reconstruct (extend hpartial))

theorem ay_mccc_report_requires_membership
    (membership_ok : Prop) (frame_ok : Prop)
    (extension_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMCCCAcceptedSatCandidate
      (AyMCCCCandidateEvidence
        membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
      audit_entry original_model ->
    membership_ok := by
  intro report
  exact ay_mccc_candidate_evidence_membership
    membership_ok frame_ok extension_ok reconstruction_ok checker_ok
    (ay_mccc_report_evidence
      (AyMCCCCandidateEvidence
        membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
      audit_entry original_model report)

theorem ay_mccc_report_requires_frame
    (membership_ok : Prop) (frame_ok : Prop)
    (extension_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMCCCAcceptedSatCandidate
      (AyMCCCCandidateEvidence
        membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
      audit_entry original_model ->
    frame_ok := by
  intro report
  exact ay_mccc_candidate_evidence_frame
    membership_ok frame_ok extension_ok reconstruction_ok checker_ok
    (ay_mccc_report_evidence
      (AyMCCCCandidateEvidence
        membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
      audit_entry original_model report)

theorem ay_mccc_report_requires_extension
    (membership_ok : Prop) (frame_ok : Prop)
    (extension_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMCCCAcceptedSatCandidate
      (AyMCCCCandidateEvidence
        membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
      audit_entry original_model ->
    extension_ok := by
  intro report
  exact ay_mccc_candidate_evidence_extension
    membership_ok frame_ok extension_ok reconstruction_ok checker_ok
    (ay_mccc_report_evidence
      (AyMCCCCandidateEvidence
        membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
      audit_entry original_model report)

theorem ay_mccc_report_requires_reconstruction
    (membership_ok : Prop) (frame_ok : Prop)
    (extension_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMCCCAcceptedSatCandidate
      (AyMCCCCandidateEvidence
        membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
      audit_entry original_model ->
    reconstruction_ok := by
  intro report
  exact ay_mccc_candidate_evidence_reconstruction
    membership_ok frame_ok extension_ok reconstruction_ok checker_ok
    (ay_mccc_report_evidence
      (AyMCCCCandidateEvidence
        membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
      audit_entry original_model report)

theorem ay_mccc_report_requires_checker
    (membership_ok : Prop) (frame_ok : Prop)
    (extension_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMCCCAcceptedSatCandidate
      (AyMCCCCandidateEvidence
        membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
      audit_entry original_model ->
    checker_ok := by
  intro report
  exact ay_mccc_candidate_evidence_checker
    membership_ok frame_ok extension_ok reconstruction_ok checker_ok
    (ay_mccc_report_evidence
      (AyMCCCCandidateEvidence
        membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
      audit_entry original_model report)

theorem ay_mccc_report_sound_exact
    (membership_ok : Prop) (frame_ok : Prop)
    (extension_ok : Prop) (reconstruction_ok : Prop)
    (checker_ok : Prop) (audit_entry : Prop)
    (original_model : Prop) :
    AyMCCCEquisat
      (AyMCCCAcceptedSatCandidate
        (AyMCCCCandidateEvidence
          membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
        audit_entry original_model)
      (AyMCCCConj
        (AyMCCCCandidateEvidence
          membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
        (AyMCCCConj audit_entry original_model)) := by
  exact ay_mccc_equisat_intro
    (AyMCCCAcceptedSatCandidate
      (AyMCCCCandidateEvidence
        membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
      audit_entry original_model)
    (AyMCCCConj
      (AyMCCCCandidateEvidence
        membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
      (AyMCCCConj audit_entry original_model))
    (fun report =>
      ay_mccc_conj_intro
        (AyMCCCCandidateEvidence
          membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
        (AyMCCCConj audit_entry original_model)
        (ay_mccc_report_evidence
          (AyMCCCCandidateEvidence
            membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
          audit_entry original_model report)
        (ay_mccc_conj_intro audit_entry original_model
          (ay_mccc_report_audit
            (AyMCCCCandidateEvidence
              membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
            audit_entry original_model report)
          (ay_mccc_report_original
            (AyMCCCCandidateEvidence
              membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
            audit_entry original_model report)))
    (fun bundle =>
      ay_mccc_report_intro
        (AyMCCCCandidateEvidence
          membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
        audit_entry original_model
        (ay_mccc_conj_left
          (AyMCCCCandidateEvidence
            membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
          (AyMCCCConj audit_entry original_model)
          bundle)
        (ay_mccc_conj_left audit_entry original_model
          (ay_mccc_conj_right
            (AyMCCCCandidateEvidence
              membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
            (AyMCCCConj audit_entry original_model)
            bundle))
        (ay_mccc_conj_right audit_entry original_model
          (ay_mccc_conj_right
            (AyMCCCCandidateEvidence
              membership_ok frame_ok extension_ok reconstruction_ok checker_ok)
            (AyMCCCConj audit_entry original_model)
            bundle)))

theorem ay_mccc_no_claim_diagnostic_intro
    (diagnostic : Prop) (public_claim : Prop) :
    diagnostic ->
    (public_claim -> False) ->
    AyMCCCNoClaimDiagnostic diagnostic public_claim := by
  intro hdiagnostic
  intro blocks
  exact ay_mccc_conj_intro diagnostic
    (public_claim -> False) hdiagnostic blocks

theorem ay_mccc_no_claim_diagnostic_reason
    (diagnostic : Prop) (public_claim : Prop) :
    AyMCCCNoClaimDiagnostic diagnostic public_claim ->
    diagnostic := by
  intro diag
  exact ay_mccc_conj_left diagnostic (public_claim -> False) diag

theorem ay_mccc_no_claim_diagnostic_blocks
    (diagnostic : Prop) (public_claim : Prop) :
    AyMCCCNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  exact ay_mccc_conj_right diagnostic (public_claim -> False) diag

theorem ay_mccc_recompute_obligation_intro
    (reason : Prop) (recompute_request : Prop) :
    reason ->
    recompute_request ->
    AyMCCCRecomputeObligation reason recompute_request := by
  intro hreason
  intro hrequest
  exact ay_mccc_conj_intro reason recompute_request hreason hrequest

theorem ay_mccc_uncovered_cube_recompute
    (uncovered_cube : Prop) (recompute_request : Prop) :
    uncovered_cube ->
    recompute_request ->
    AyMCCCRecomputeObligation uncovered_cube recompute_request := by
  intro huncovered
  intro hrequest
  exact ay_mccc_recompute_obligation_intro
    uncovered_cube recompute_request huncovered hrequest

theorem ay_mccc_uncovered_cube_no_claim
    (uncovered_cube : Prop) (public_claim : Prop) :
    uncovered_cube ->
    (public_claim -> uncovered_cube -> False) ->
    AyMCCCNoClaimDiagnostic uncovered_cube public_claim := by
  intro huncovered
  intro blocks
  exact ay_mccc_no_claim_diagnostic_intro
    uncovered_cube public_claim huncovered
    (fun claim => blocks claim huncovered)

theorem ay_mccc_frame_mismatch_no_claim
    (frame_mismatch : Prop) (public_claim : Prop) :
    frame_mismatch ->
    (public_claim -> frame_mismatch -> False) ->
    AyMCCCNoClaimDiagnostic frame_mismatch public_claim := by
  intro hmismatch
  intro blocks
  exact ay_mccc_no_claim_diagnostic_intro
    frame_mismatch public_claim hmismatch
    (fun claim => blocks claim hmismatch)

theorem ay_mccc_checker_reject_no_claim
    (checker_reject : Prop) (public_claim : Prop) :
    checker_reject ->
    (public_claim -> checker_reject -> False) ->
    AyMCCCNoClaimDiagnostic checker_reject public_claim := by
  intro hreject
  intro blocks
  exact ay_mccc_no_claim_diagnostic_intro
    checker_reject public_claim hreject
    (fun claim => blocks claim hreject)

theorem ay_mccc_diagnostic_blocks_public_claim
    (diagnostic : Prop) (public_claim : Prop) :
    AyMCCCNoClaimDiagnostic diagnostic public_claim ->
    public_claim ->
    False := by
  intro diag
  intro claim
  exact ay_mccc_no_claim_diagnostic_blocks
    diagnostic public_claim diag claim

theorem ay_mccc_bad_candidate_no_stale_sat
    (uncovered_cube : Prop) (frame_mismatch : Prop)
    (checker_reject : Prop) (public_claim : Prop) :
    (public_claim -> uncovered_cube -> False) ->
    (public_claim -> frame_mismatch -> False) ->
    (public_claim -> checker_reject -> False) ->
    AyMCCCConj
      (uncovered_cube ->
        AyMCCCNoClaimDiagnostic uncovered_cube public_claim)
      (AyMCCCConj
        (frame_mismatch ->
          AyMCCCNoClaimDiagnostic frame_mismatch public_claim)
        (checker_reject ->
          AyMCCCNoClaimDiagnostic checker_reject public_claim)) := by
  intro uncovered_blocks
  intro frame_blocks
  intro checker_blocks
  exact ay_mccc_conj_intro
    (uncovered_cube ->
      AyMCCCNoClaimDiagnostic uncovered_cube public_claim)
    (AyMCCCConj
      (frame_mismatch ->
        AyMCCCNoClaimDiagnostic frame_mismatch public_claim)
      (checker_reject ->
        AyMCCCNoClaimDiagnostic checker_reject public_claim))
    (fun huncovered =>
      ay_mccc_uncovered_cube_no_claim
        uncovered_cube public_claim huncovered uncovered_blocks)
    (ay_mccc_conj_intro
      (frame_mismatch ->
        AyMCCCNoClaimDiagnostic frame_mismatch public_claim)
      (checker_reject ->
        AyMCCCNoClaimDiagnostic checker_reject public_claim)
      (fun hmismatch =>
        ay_mccc_frame_mismatch_no_claim
          frame_mismatch public_claim hmismatch frame_blocks)
      (fun hreject =>
        ay_mccc_checker_reject_no_claim
          checker_reject public_claim hreject checker_blocks))

