-- SAT-COMP/ay refined cube/model result lift soundness skeleton.
-- A child/refined cube result may be lifted to the original formula only when
-- coverage, reconstruction, assignment compatibility, fingerprints, and replay
-- evidence agree.

def AyMRRLConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMRRLDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMRRLEquisat (left right : Prop) : Prop :=
  AyMRRLConj (left -> right) (right -> left)

def AyMRRLParentCoverage
    (parentCovered childCovered childImpliesParent : Prop) : Prop :=
  AyMRRLConj parentCovered
    (AyMRRLConj childCovered childImpliesParent)

def AyMRRLProjectionReconstruction
    (projectionEvidence reconstructionEvidence : Prop) : Prop :=
  AyMRRLConj projectionEvidence reconstructionEvidence

def AyMRRLAssignmentCompatibility
    (childAssignment parentAssignment originalAssignment : Prop) : Prop :=
  AyMRRLConj childAssignment
    (AyMRRLConj parentAssignment originalAssignment)

def AyMRRLFormulaFingerprint
    (childFingerprint parentFingerprint originalFingerprint : Prop) : Prop :=
  AyMRRLConj childFingerprint
    (AyMRRLConj parentFingerprint originalFingerprint)

def AyMRRLCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMRRLConj checkerAccepted replayTrace

def AyMRRLResultLiftEvidence
    (coverageOk projectionOk assignmentOk fingerprintOk replayOk : Prop) :
    Prop :=
  AyMRRLConj coverageOk
    (AyMRRLConj projectionOk
      (AyMRRLConj assignmentOk
        (AyMRRLConj fingerprintOk replayOk)))

def AyMRRLLiftedResultClaim
    (liftEvidence auditEntry publicResult : Prop) : Prop :=
  AyMRRLConj liftEvidence (AyMRRLConj auditEntry publicResult)

def AyMRRLNoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMRRLConj diagnostic (publicClaim -> False)

def AyMRRLRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMRRLConj reason recomputeRequest

theorem ay_mrrl_conj_intro {left right : Prop} :
    left -> right -> AyMRRLConj left right :=
  fun hleft hright goal k => k hleft hright

theorem ay_mrrl_conj_left {left right : Prop} :
    AyMRRLConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mrrl_conj_right {left right : Prop} :
    AyMRRLConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mrrl_disj_left {left right : Prop} :
    left -> AyMRRLDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mrrl_disj_right {left right : Prop} :
    right -> AyMRRLDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mrrl_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMRRLEquisat left right :=
  fun hf hb => ay_mrrl_conj_intro hf hb

theorem ay_mrrl_equisat_forward {left right : Prop} :
    AyMRRLEquisat left right -> left -> right :=
  fun h => ay_mrrl_conj_left h

theorem ay_mrrl_equisat_backward {left right : Prop} :
    AyMRRLEquisat left right -> right -> left :=
  fun h => ay_mrrl_conj_right h

theorem ay_mrrl_parent_coverage_intro
    {parentCovered childCovered childImpliesParent : Prop} :
    parentCovered ->
    childCovered ->
    childImpliesParent ->
    AyMRRLParentCoverage parentCovered childCovered childImpliesParent :=
  fun hparent hchild himplies =>
    ay_mrrl_conj_intro hparent
      (ay_mrrl_conj_intro hchild himplies)

theorem ay_mrrl_parent_coverage_parent
    {parentCovered childCovered childImpliesParent : Prop} :
    AyMRRLParentCoverage parentCovered childCovered childImpliesParent ->
    parentCovered :=
  fun h => ay_mrrl_conj_left h

theorem ay_mrrl_parent_coverage_child
    {parentCovered childCovered childImpliesParent : Prop} :
    AyMRRLParentCoverage parentCovered childCovered childImpliesParent ->
    childCovered :=
  fun h => ay_mrrl_conj_left (ay_mrrl_conj_right h)

theorem ay_mrrl_parent_coverage_child_implies_parent
    {parentCovered childCovered childImpliesParent : Prop} :
    AyMRRLParentCoverage parentCovered childCovered childImpliesParent ->
    childImpliesParent :=
  fun h => ay_mrrl_conj_right (ay_mrrl_conj_right h)

theorem ay_mrrl_projection_reconstruction_intro
    {projectionEvidence reconstructionEvidence : Prop} :
    projectionEvidence ->
    reconstructionEvidence ->
    AyMRRLProjectionReconstruction
      projectionEvidence reconstructionEvidence :=
  fun hprojection hreconstruction =>
    ay_mrrl_conj_intro hprojection hreconstruction

theorem ay_mrrl_projection_reconstruction_projection
    {projectionEvidence reconstructionEvidence : Prop} :
    AyMRRLProjectionReconstruction
      projectionEvidence reconstructionEvidence ->
    projectionEvidence :=
  fun h => ay_mrrl_conj_left h

theorem ay_mrrl_projection_reconstruction_reconstruction
    {projectionEvidence reconstructionEvidence : Prop} :
    AyMRRLProjectionReconstruction
      projectionEvidence reconstructionEvidence ->
    reconstructionEvidence :=
  fun h => ay_mrrl_conj_right h

theorem ay_mrrl_assignment_compatibility_intro
    {childAssignment parentAssignment originalAssignment : Prop} :
    childAssignment ->
    parentAssignment ->
    originalAssignment ->
    AyMRRLAssignmentCompatibility
      childAssignment parentAssignment originalAssignment :=
  fun hchild hparent horiginal =>
    ay_mrrl_conj_intro hchild
      (ay_mrrl_conj_intro hparent horiginal)

theorem ay_mrrl_assignment_compatibility_child
    {childAssignment parentAssignment originalAssignment : Prop} :
    AyMRRLAssignmentCompatibility
      childAssignment parentAssignment originalAssignment ->
    childAssignment :=
  fun h => ay_mrrl_conj_left h

theorem ay_mrrl_assignment_compatibility_parent
    {childAssignment parentAssignment originalAssignment : Prop} :
    AyMRRLAssignmentCompatibility
      childAssignment parentAssignment originalAssignment ->
    parentAssignment :=
  fun h => ay_mrrl_conj_left (ay_mrrl_conj_right h)

theorem ay_mrrl_assignment_compatibility_original
    {childAssignment parentAssignment originalAssignment : Prop} :
    AyMRRLAssignmentCompatibility
      childAssignment parentAssignment originalAssignment ->
    originalAssignment :=
  fun h => ay_mrrl_conj_right (ay_mrrl_conj_right h)

theorem ay_mrrl_formula_fingerprint_intro
    {childFingerprint parentFingerprint originalFingerprint : Prop} :
    childFingerprint ->
    parentFingerprint ->
    originalFingerprint ->
    AyMRRLFormulaFingerprint
      childFingerprint parentFingerprint originalFingerprint :=
  fun hchild hparent horiginal =>
    ay_mrrl_conj_intro hchild
      (ay_mrrl_conj_intro hparent horiginal)

theorem ay_mrrl_formula_fingerprint_child
    {childFingerprint parentFingerprint originalFingerprint : Prop} :
    AyMRRLFormulaFingerprint
      childFingerprint parentFingerprint originalFingerprint ->
    childFingerprint :=
  fun h => ay_mrrl_conj_left h

theorem ay_mrrl_formula_fingerprint_parent
    {childFingerprint parentFingerprint originalFingerprint : Prop} :
    AyMRRLFormulaFingerprint
      childFingerprint parentFingerprint originalFingerprint ->
    parentFingerprint :=
  fun h => ay_mrrl_conj_left (ay_mrrl_conj_right h)

theorem ay_mrrl_formula_fingerprint_original
    {childFingerprint parentFingerprint originalFingerprint : Prop} :
    AyMRRLFormulaFingerprint
      childFingerprint parentFingerprint originalFingerprint ->
    originalFingerprint :=
  fun h => ay_mrrl_conj_right (ay_mrrl_conj_right h)

theorem ay_mrrl_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMRRLCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mrrl_conj_intro haccepted htrace

theorem ay_mrrl_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMRRLCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_mrrl_conj_left h

theorem ay_mrrl_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMRRLCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_mrrl_conj_right h

theorem ay_mrrl_result_lift_evidence_intro
    {coverageOk projectionOk assignmentOk fingerprintOk replayOk : Prop} :
    coverageOk ->
    projectionOk ->
    assignmentOk ->
    fingerprintOk ->
    replayOk ->
    AyMRRLResultLiftEvidence
      coverageOk projectionOk assignmentOk fingerprintOk replayOk :=
  fun hcoverage hprojection hassignment hfingerprint hreplay =>
    ay_mrrl_conj_intro hcoverage
      (ay_mrrl_conj_intro hprojection
        (ay_mrrl_conj_intro hassignment
          (ay_mrrl_conj_intro hfingerprint hreplay)))

theorem ay_mrrl_result_lift_evidence_coverage
    {coverageOk projectionOk assignmentOk fingerprintOk replayOk : Prop} :
    AyMRRLResultLiftEvidence
      coverageOk projectionOk assignmentOk fingerprintOk replayOk ->
    coverageOk :=
  fun h => ay_mrrl_conj_left h

theorem ay_mrrl_result_lift_evidence_projection
    {coverageOk projectionOk assignmentOk fingerprintOk replayOk : Prop} :
    AyMRRLResultLiftEvidence
      coverageOk projectionOk assignmentOk fingerprintOk replayOk ->
    projectionOk :=
  fun h => ay_mrrl_conj_left (ay_mrrl_conj_right h)

theorem ay_mrrl_result_lift_evidence_assignment
    {coverageOk projectionOk assignmentOk fingerprintOk replayOk : Prop} :
    AyMRRLResultLiftEvidence
      coverageOk projectionOk assignmentOk fingerprintOk replayOk ->
    assignmentOk :=
  fun h => ay_mrrl_conj_left (ay_mrrl_conj_right (ay_mrrl_conj_right h))

theorem ay_mrrl_result_lift_evidence_fingerprint
    {coverageOk projectionOk assignmentOk fingerprintOk replayOk : Prop} :
    AyMRRLResultLiftEvidence
      coverageOk projectionOk assignmentOk fingerprintOk replayOk ->
    fingerprintOk :=
  fun h =>
    ay_mrrl_conj_left
      (ay_mrrl_conj_right (ay_mrrl_conj_right (ay_mrrl_conj_right h)))

theorem ay_mrrl_result_lift_evidence_replay
    {coverageOk projectionOk assignmentOk fingerprintOk replayOk : Prop} :
    AyMRRLResultLiftEvidence
      coverageOk projectionOk assignmentOk fingerprintOk replayOk ->
    replayOk :=
  fun h =>
    ay_mrrl_conj_right
      (ay_mrrl_conj_right (ay_mrrl_conj_right (ay_mrrl_conj_right h)))

theorem ay_mrrl_lifted_result_claim_intro
    {liftEvidence auditEntry publicResult : Prop} :
    liftEvidence ->
    auditEntry ->
    publicResult ->
    AyMRRLLiftedResultClaim liftEvidence auditEntry publicResult :=
  fun hevidence haudit hresult =>
    ay_mrrl_conj_intro hevidence (ay_mrrl_conj_intro haudit hresult)

theorem ay_mrrl_lifted_result_claim_evidence
    {liftEvidence auditEntry publicResult : Prop} :
    AyMRRLLiftedResultClaim liftEvidence auditEntry publicResult ->
    liftEvidence :=
  fun h => ay_mrrl_conj_left h

theorem ay_mrrl_lifted_result_claim_audit
    {liftEvidence auditEntry publicResult : Prop} :
    AyMRRLLiftedResultClaim liftEvidence auditEntry publicResult ->
    auditEntry :=
  fun h => ay_mrrl_conj_left (ay_mrrl_conj_right h)

theorem ay_mrrl_lifted_result_claim_result
    {liftEvidence auditEntry publicResult : Prop} :
    AyMRRLLiftedResultClaim liftEvidence auditEntry publicResult ->
    publicResult :=
  fun h => ay_mrrl_conj_right (ay_mrrl_conj_right h)

theorem ay_mrrl_claim_requires_coverage
    {coverageOk projectionOk assignmentOk fingerprintOk replayOk auditEntry
      publicResult : Prop} :
    AyMRRLLiftedResultClaim
      (AyMRRLResultLiftEvidence
        coverageOk projectionOk assignmentOk fingerprintOk replayOk)
      auditEntry
      publicResult ->
    coverageOk :=
  fun h =>
    ay_mrrl_result_lift_evidence_coverage
      (ay_mrrl_lifted_result_claim_evidence h)

theorem ay_mrrl_claim_requires_projection
    {coverageOk projectionOk assignmentOk fingerprintOk replayOk auditEntry
      publicResult : Prop} :
    AyMRRLLiftedResultClaim
      (AyMRRLResultLiftEvidence
        coverageOk projectionOk assignmentOk fingerprintOk replayOk)
      auditEntry
      publicResult ->
    projectionOk :=
  fun h =>
    ay_mrrl_result_lift_evidence_projection
      (ay_mrrl_lifted_result_claim_evidence h)

theorem ay_mrrl_claim_requires_assignment
    {coverageOk projectionOk assignmentOk fingerprintOk replayOk auditEntry
      publicResult : Prop} :
    AyMRRLLiftedResultClaim
      (AyMRRLResultLiftEvidence
        coverageOk projectionOk assignmentOk fingerprintOk replayOk)
      auditEntry
      publicResult ->
    assignmentOk :=
  fun h =>
    ay_mrrl_result_lift_evidence_assignment
      (ay_mrrl_lifted_result_claim_evidence h)

theorem ay_mrrl_claim_requires_fingerprint
    {coverageOk projectionOk assignmentOk fingerprintOk replayOk auditEntry
      publicResult : Prop} :
    AyMRRLLiftedResultClaim
      (AyMRRLResultLiftEvidence
        coverageOk projectionOk assignmentOk fingerprintOk replayOk)
      auditEntry
      publicResult ->
    fingerprintOk :=
  fun h =>
    ay_mrrl_result_lift_evidence_fingerprint
      (ay_mrrl_lifted_result_claim_evidence h)

theorem ay_mrrl_claim_requires_replay
    {coverageOk projectionOk assignmentOk fingerprintOk replayOk auditEntry
      publicResult : Prop} :
    AyMRRLLiftedResultClaim
      (AyMRRLResultLiftEvidence
        coverageOk projectionOk assignmentOk fingerprintOk replayOk)
      auditEntry
      publicResult ->
    replayOk :=
  fun h =>
    ay_mrrl_result_lift_evidence_replay
      (ay_mrrl_lifted_result_claim_evidence h)

theorem ay_mrrl_accepted_lift_preserves_sat_claim
    {liftEvidence auditEntry publicSatClaim : Prop} :
    AyMRRLLiftedResultClaim liftEvidence auditEntry publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mrrl_lifted_result_claim_result h

theorem ay_mrrl_accepted_lift_preserves_unsat_claim
    {liftEvidence auditEntry publicUnsatClaim : Prop} :
    AyMRRLLiftedResultClaim liftEvidence auditEntry publicUnsatClaim ->
    publicUnsatClaim :=
  fun h => ay_mrrl_lifted_result_claim_result h

theorem ay_mrrl_lifted_result_claim_sound_exact
    {liftEvidence auditEntry publicResult : Prop} :
    AyMRRLEquisat
      (AyMRRLLiftedResultClaim liftEvidence auditEntry publicResult)
      (AyMRRLConj liftEvidence (AyMRRLConj auditEntry publicResult)) :=
  ay_mrrl_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_mrrl_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMRRLNoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_mrrl_conj_intro hdiagnostic hblocks

theorem ay_mrrl_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMRRLNoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_mrrl_conj_left h

theorem ay_mrrl_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMRRLNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_mrrl_conj_right h

theorem ay_mrrl_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMRRLRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_mrrl_conj_intro hreason hrequest

theorem ay_mrrl_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMRRLRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_mrrl_conj_left h

theorem ay_mrrl_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMRRLRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_mrrl_conj_right h

theorem ay_mrrl_stale_parent_frame_recompute
    {staleParentFrame recomputeRequest : Prop} :
    staleParentFrame ->
    recomputeRequest ->
    AyMRRLRecomputeObligation staleParentFrame recomputeRequest :=
  fun hstale hrecompute =>
    ay_mrrl_recompute_obligation_intro hstale hrecompute

theorem ay_mrrl_stale_parent_frame_no_claim
    {staleParentFrame publicClaim : Prop} :
    staleParentFrame ->
    (staleParentFrame -> publicClaim -> False) ->
    AyMRRLNoClaimDiagnostic staleParentFrame publicClaim :=
  fun hstale hblocks =>
    ay_mrrl_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_mrrl_uncovered_child_cube_no_claim
    {uncoveredChildCube publicClaim : Prop} :
    uncoveredChildCube ->
    (uncoveredChildCube -> publicClaim -> False) ->
    AyMRRLNoClaimDiagnostic uncoveredChildCube publicClaim :=
  fun huncovered hblocks =>
    ay_mrrl_no_claim_diagnostic_intro huncovered (hblocks huncovered)

theorem ay_mrrl_projection_mismatch_no_claim
    {projectionMismatch publicClaim : Prop} :
    projectionMismatch ->
    (projectionMismatch -> publicClaim -> False) ->
    AyMRRLNoClaimDiagnostic projectionMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mrrl_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mrrl_assignment_mismatch_no_claim
    {assignmentMismatch publicClaim : Prop} :
    assignmentMismatch ->
    (assignmentMismatch -> publicClaim -> False) ->
    AyMRRLNoClaimDiagnostic assignmentMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mrrl_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mrrl_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicClaim : Prop} :
    fingerprintMismatch ->
    (fingerprintMismatch -> publicClaim -> False) ->
    AyMRRLNoClaimDiagnostic fingerprintMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mrrl_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mrrl_replay_rejection_no_claim
    {replayRejection publicClaim : Prop} :
    replayRejection ->
    (replayRejection -> publicClaim -> False) ->
    AyMRRLNoClaimDiagnostic replayRejection publicClaim :=
  fun hreject hblocks =>
    ay_mrrl_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_mrrl_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMRRLNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_mrrl_no_claim_diagnostic_blocks h hclaim

theorem ay_mrrl_bad_lift_no_stale_public_result
    {staleParentFrame uncoveredChildCube projectionMismatch assignmentMismatch
      fingerprintMismatch replayRejection publicClaim : Prop} :
    (staleParentFrame -> publicClaim -> False) ->
    (uncoveredChildCube -> publicClaim -> False) ->
    (projectionMismatch -> publicClaim -> False) ->
    (assignmentMismatch -> publicClaim -> False) ->
    (fingerprintMismatch -> publicClaim -> False) ->
    (replayRejection -> publicClaim -> False) ->
    AyMRRLConj
      (staleParentFrame ->
        AyMRRLNoClaimDiagnostic staleParentFrame publicClaim)
      (AyMRRLConj
        (uncoveredChildCube ->
          AyMRRLNoClaimDiagnostic uncoveredChildCube publicClaim)
        (AyMRRLConj
          (projectionMismatch ->
            AyMRRLNoClaimDiagnostic projectionMismatch publicClaim)
          (AyMRRLConj
            (assignmentMismatch ->
              AyMRRLNoClaimDiagnostic assignmentMismatch publicClaim)
            (AyMRRLConj
              (fingerprintMismatch ->
                AyMRRLNoClaimDiagnostic fingerprintMismatch publicClaim)
              (replayRejection ->
                AyMRRLNoClaimDiagnostic replayRejection publicClaim))))) :=
  fun hstale huncovered hprojection hassignment hfingerprint hreplay =>
    ay_mrrl_conj_intro
      (fun h => ay_mrrl_stale_parent_frame_no_claim h hstale)
      (ay_mrrl_conj_intro
        (fun h => ay_mrrl_uncovered_child_cube_no_claim h huncovered)
        (ay_mrrl_conj_intro
          (fun h => ay_mrrl_projection_mismatch_no_claim h hprojection)
          (ay_mrrl_conj_intro
            (fun h => ay_mrrl_assignment_mismatch_no_claim h hassignment)
            (ay_mrrl_conj_intro
              (fun h =>
                ay_mrrl_fingerprint_mismatch_no_claim h hfingerprint)
              (fun h => ay_mrrl_replay_rejection_no_claim h hreplay)))))
