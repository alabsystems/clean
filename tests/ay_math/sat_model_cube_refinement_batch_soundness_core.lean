-- SAT-COMP/ay cube-refinement batch soundness skeleton.
-- A refined cube batch inherits coverage from parent cubes only when the
-- refinement map, core guidance, child coverage, frame, reconstruction, and
-- checker replay evidence agree.

def AyMCRBConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMCRBDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMCRBEquisat (left right : Prop) : Prop :=
  AyMCRBConj (left -> right) (right -> left)

def AyMCRBRefinementMap
    (parentBatch childBatch mapWitness : Prop) : Prop :=
  AyMCRBConj parentBatch (AyMCRBConj childBatch mapWitness)

def AyMCRBCoreGuidance
    (coreMembership coreFreshness guidanceApplied : Prop) : Prop :=
  AyMCRBConj coreMembership
    (AyMCRBConj coreFreshness guidanceApplied)

def AyMCRBChildCoverage
    (parentCovered childCoversParent noUncoveredChild : Prop) : Prop :=
  AyMCRBConj parentCovered
    (AyMCRBConj childCoversParent noUncoveredChild)

def AyMCRBParentFrame
    (parentFrameId assumptionFrame cubeBatchId : Prop) : Prop :=
  AyMCRBConj parentFrameId (AyMCRBConj assumptionFrame cubeBatchId)

def AyMCRBProjectionReconstruction
    (projectionEvidence reconstructionEvidence : Prop) : Prop :=
  AyMCRBConj projectionEvidence reconstructionEvidence

def AyMCRBCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMCRBConj checkerAccepted replayTrace

def AyMCRBBatchEvidence
    (refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk : Prop) : Prop :=
  AyMCRBConj refinementMapOk
    (AyMCRBConj coreGuidanceOk
      (AyMCRBConj childCoverageOk
        (AyMCRBConj frameOk
          (AyMCRBConj projectionOk replayOk))))

def AyMCRBRefinedBatchClaim
    (batchEvidence auditEntry publicResult : Prop) : Prop :=
  AyMCRBConj batchEvidence (AyMCRBConj auditEntry publicResult)

def AyMCRBNoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMCRBConj diagnostic (publicClaim -> False)

def AyMCRBRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMCRBConj reason recomputeRequest

theorem ay_mcrb_conj_intro {left right : Prop} :
    left -> right -> AyMCRBConj left right :=
  fun hleft hright goal k => k hleft hright

theorem ay_mcrb_conj_left {left right : Prop} :
    AyMCRBConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mcrb_conj_right {left right : Prop} :
    AyMCRBConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mcrb_disj_left {left right : Prop} :
    left -> AyMCRBDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mcrb_disj_right {left right : Prop} :
    right -> AyMCRBDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mcrb_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMCRBEquisat left right :=
  fun hf hb => ay_mcrb_conj_intro hf hb

theorem ay_mcrb_equisat_forward {left right : Prop} :
    AyMCRBEquisat left right -> left -> right :=
  fun h => ay_mcrb_conj_left h

theorem ay_mcrb_equisat_backward {left right : Prop} :
    AyMCRBEquisat left right -> right -> left :=
  fun h => ay_mcrb_conj_right h

theorem ay_mcrb_refinement_map_intro
    {parentBatch childBatch mapWitness : Prop} :
    parentBatch ->
    childBatch ->
    mapWitness ->
    AyMCRBRefinementMap parentBatch childBatch mapWitness :=
  fun hparent hchild hmap =>
    ay_mcrb_conj_intro hparent (ay_mcrb_conj_intro hchild hmap)

theorem ay_mcrb_refinement_map_parent
    {parentBatch childBatch mapWitness : Prop} :
    AyMCRBRefinementMap parentBatch childBatch mapWitness ->
    parentBatch :=
  fun h => ay_mcrb_conj_left h

theorem ay_mcrb_refinement_map_child
    {parentBatch childBatch mapWitness : Prop} :
    AyMCRBRefinementMap parentBatch childBatch mapWitness ->
    childBatch :=
  fun h => ay_mcrb_conj_left (ay_mcrb_conj_right h)

theorem ay_mcrb_refinement_map_witness
    {parentBatch childBatch mapWitness : Prop} :
    AyMCRBRefinementMap parentBatch childBatch mapWitness ->
    mapWitness :=
  fun h => ay_mcrb_conj_right (ay_mcrb_conj_right h)

theorem ay_mcrb_core_guidance_intro
    {coreMembership coreFreshness guidanceApplied : Prop} :
    coreMembership ->
    coreFreshness ->
    guidanceApplied ->
    AyMCRBCoreGuidance coreMembership coreFreshness guidanceApplied :=
  fun hmember hfresh happlied =>
    ay_mcrb_conj_intro hmember (ay_mcrb_conj_intro hfresh happlied)

theorem ay_mcrb_core_guidance_membership
    {coreMembership coreFreshness guidanceApplied : Prop} :
    AyMCRBCoreGuidance coreMembership coreFreshness guidanceApplied ->
    coreMembership :=
  fun h => ay_mcrb_conj_left h

theorem ay_mcrb_core_guidance_freshness
    {coreMembership coreFreshness guidanceApplied : Prop} :
    AyMCRBCoreGuidance coreMembership coreFreshness guidanceApplied ->
    coreFreshness :=
  fun h => ay_mcrb_conj_left (ay_mcrb_conj_right h)

theorem ay_mcrb_core_guidance_applied
    {coreMembership coreFreshness guidanceApplied : Prop} :
    AyMCRBCoreGuidance coreMembership coreFreshness guidanceApplied ->
    guidanceApplied :=
  fun h => ay_mcrb_conj_right (ay_mcrb_conj_right h)

theorem ay_mcrb_child_coverage_intro
    {parentCovered childCoversParent noUncoveredChild : Prop} :
    parentCovered ->
    childCoversParent ->
    noUncoveredChild ->
    AyMCRBChildCoverage parentCovered childCoversParent noUncoveredChild :=
  fun hparent hchild huncovered =>
    ay_mcrb_conj_intro hparent
      (ay_mcrb_conj_intro hchild huncovered)

theorem ay_mcrb_child_coverage_parent
    {parentCovered childCoversParent noUncoveredChild : Prop} :
    AyMCRBChildCoverage parentCovered childCoversParent noUncoveredChild ->
    parentCovered :=
  fun h => ay_mcrb_conj_left h

theorem ay_mcrb_child_coverage_child
    {parentCovered childCoversParent noUncoveredChild : Prop} :
    AyMCRBChildCoverage parentCovered childCoversParent noUncoveredChild ->
    childCoversParent :=
  fun h => ay_mcrb_conj_left (ay_mcrb_conj_right h)

theorem ay_mcrb_child_coverage_no_uncovered
    {parentCovered childCoversParent noUncoveredChild : Prop} :
    AyMCRBChildCoverage parentCovered childCoversParent noUncoveredChild ->
    noUncoveredChild :=
  fun h => ay_mcrb_conj_right (ay_mcrb_conj_right h)

theorem ay_mcrb_parent_frame_intro
    {parentFrameId assumptionFrame cubeBatchId : Prop} :
    parentFrameId ->
    assumptionFrame ->
    cubeBatchId ->
    AyMCRBParentFrame parentFrameId assumptionFrame cubeBatchId :=
  fun hparent hframe hbatch =>
    ay_mcrb_conj_intro hparent (ay_mcrb_conj_intro hframe hbatch)

theorem ay_mcrb_parent_frame_id
    {parentFrameId assumptionFrame cubeBatchId : Prop} :
    AyMCRBParentFrame parentFrameId assumptionFrame cubeBatchId ->
    parentFrameId :=
  fun h => ay_mcrb_conj_left h

theorem ay_mcrb_parent_frame_assumption
    {parentFrameId assumptionFrame cubeBatchId : Prop} :
    AyMCRBParentFrame parentFrameId assumptionFrame cubeBatchId ->
    assumptionFrame :=
  fun h => ay_mcrb_conj_left (ay_mcrb_conj_right h)

theorem ay_mcrb_parent_frame_batch
    {parentFrameId assumptionFrame cubeBatchId : Prop} :
    AyMCRBParentFrame parentFrameId assumptionFrame cubeBatchId ->
    cubeBatchId :=
  fun h => ay_mcrb_conj_right (ay_mcrb_conj_right h)

theorem ay_mcrb_projection_reconstruction_intro
    {projectionEvidence reconstructionEvidence : Prop} :
    projectionEvidence ->
    reconstructionEvidence ->
    AyMCRBProjectionReconstruction
      projectionEvidence reconstructionEvidence :=
  fun hprojection hreconstruction =>
    ay_mcrb_conj_intro hprojection hreconstruction

theorem ay_mcrb_projection_reconstruction_projection
    {projectionEvidence reconstructionEvidence : Prop} :
    AyMCRBProjectionReconstruction
      projectionEvidence reconstructionEvidence ->
    projectionEvidence :=
  fun h => ay_mcrb_conj_left h

theorem ay_mcrb_projection_reconstruction_reconstruction
    {projectionEvidence reconstructionEvidence : Prop} :
    AyMCRBProjectionReconstruction
      projectionEvidence reconstructionEvidence ->
    reconstructionEvidence :=
  fun h => ay_mcrb_conj_right h

theorem ay_mcrb_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMCRBCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mcrb_conj_intro haccepted htrace

theorem ay_mcrb_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMCRBCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_mcrb_conj_left h

theorem ay_mcrb_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMCRBCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_mcrb_conj_right h

theorem ay_mcrb_batch_evidence_intro
    {refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk : Prop} :
    refinementMapOk ->
    coreGuidanceOk ->
    childCoverageOk ->
    frameOk ->
    projectionOk ->
    replayOk ->
    AyMCRBBatchEvidence
      refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk :=
  fun hmap hcore hcoverage hframe hprojection hreplay =>
    ay_mcrb_conj_intro hmap
      (ay_mcrb_conj_intro hcore
        (ay_mcrb_conj_intro hcoverage
          (ay_mcrb_conj_intro hframe
            (ay_mcrb_conj_intro hprojection hreplay))))

theorem ay_mcrb_batch_evidence_refinement_map
    {refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk : Prop} :
    AyMCRBBatchEvidence
      refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk ->
    refinementMapOk :=
  fun h => ay_mcrb_conj_left h

theorem ay_mcrb_batch_evidence_core_guidance
    {refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk : Prop} :
    AyMCRBBatchEvidence
      refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk ->
    coreGuidanceOk :=
  fun h => ay_mcrb_conj_left (ay_mcrb_conj_right h)

theorem ay_mcrb_batch_evidence_child_coverage
    {refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk : Prop} :
    AyMCRBBatchEvidence
      refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk ->
    childCoverageOk :=
  fun h => ay_mcrb_conj_left (ay_mcrb_conj_right (ay_mcrb_conj_right h))

theorem ay_mcrb_batch_evidence_frame
    {refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk : Prop} :
    AyMCRBBatchEvidence
      refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk ->
    frameOk :=
  fun h =>
    ay_mcrb_conj_left
      (ay_mcrb_conj_right (ay_mcrb_conj_right (ay_mcrb_conj_right h)))

theorem ay_mcrb_batch_evidence_projection
    {refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk : Prop} :
    AyMCRBBatchEvidence
      refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk ->
    projectionOk :=
  fun h =>
    ay_mcrb_conj_left
      (ay_mcrb_conj_right
        (ay_mcrb_conj_right (ay_mcrb_conj_right (ay_mcrb_conj_right h))))

theorem ay_mcrb_batch_evidence_replay
    {refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk : Prop} :
    AyMCRBBatchEvidence
      refinementMapOk coreGuidanceOk childCoverageOk frameOk
      projectionOk replayOk ->
    replayOk :=
  fun h =>
    ay_mcrb_conj_right
      (ay_mcrb_conj_right
        (ay_mcrb_conj_right (ay_mcrb_conj_right (ay_mcrb_conj_right h))))

theorem ay_mcrb_refined_batch_claim_intro
    {batchEvidence auditEntry publicResult : Prop} :
    batchEvidence ->
    auditEntry ->
    publicResult ->
    AyMCRBRefinedBatchClaim batchEvidence auditEntry publicResult :=
  fun hevidence haudit hresult =>
    ay_mcrb_conj_intro hevidence (ay_mcrb_conj_intro haudit hresult)

theorem ay_mcrb_refined_batch_claim_evidence
    {batchEvidence auditEntry publicResult : Prop} :
    AyMCRBRefinedBatchClaim batchEvidence auditEntry publicResult ->
    batchEvidence :=
  fun h => ay_mcrb_conj_left h

theorem ay_mcrb_refined_batch_claim_audit
    {batchEvidence auditEntry publicResult : Prop} :
    AyMCRBRefinedBatchClaim batchEvidence auditEntry publicResult ->
    auditEntry :=
  fun h => ay_mcrb_conj_left (ay_mcrb_conj_right h)

theorem ay_mcrb_refined_batch_claim_result
    {batchEvidence auditEntry publicResult : Prop} :
    AyMCRBRefinedBatchClaim batchEvidence auditEntry publicResult ->
    publicResult :=
  fun h => ay_mcrb_conj_right (ay_mcrb_conj_right h)

theorem ay_mcrb_claim_requires_refinement_map
    {refinementMapOk coreGuidanceOk childCoverageOk frameOk projectionOk
      replayOk auditEntry publicResult : Prop} :
    AyMCRBRefinedBatchClaim
      (AyMCRBBatchEvidence
        refinementMapOk coreGuidanceOk childCoverageOk frameOk
        projectionOk replayOk)
      auditEntry
      publicResult ->
    refinementMapOk :=
  fun h =>
    ay_mcrb_batch_evidence_refinement_map
      (ay_mcrb_refined_batch_claim_evidence h)

theorem ay_mcrb_claim_requires_core_guidance
    {refinementMapOk coreGuidanceOk childCoverageOk frameOk projectionOk
      replayOk auditEntry publicResult : Prop} :
    AyMCRBRefinedBatchClaim
      (AyMCRBBatchEvidence
        refinementMapOk coreGuidanceOk childCoverageOk frameOk
        projectionOk replayOk)
      auditEntry
      publicResult ->
    coreGuidanceOk :=
  fun h =>
    ay_mcrb_batch_evidence_core_guidance
      (ay_mcrb_refined_batch_claim_evidence h)

theorem ay_mcrb_claim_requires_child_coverage
    {refinementMapOk coreGuidanceOk childCoverageOk frameOk projectionOk
      replayOk auditEntry publicResult : Prop} :
    AyMCRBRefinedBatchClaim
      (AyMCRBBatchEvidence
        refinementMapOk coreGuidanceOk childCoverageOk frameOk
        projectionOk replayOk)
      auditEntry
      publicResult ->
    childCoverageOk :=
  fun h =>
    ay_mcrb_batch_evidence_child_coverage
      (ay_mcrb_refined_batch_claim_evidence h)

theorem ay_mcrb_claim_requires_parent_frame
    {refinementMapOk coreGuidanceOk childCoverageOk frameOk projectionOk
      replayOk auditEntry publicResult : Prop} :
    AyMCRBRefinedBatchClaim
      (AyMCRBBatchEvidence
        refinementMapOk coreGuidanceOk childCoverageOk frameOk
        projectionOk replayOk)
      auditEntry
      publicResult ->
    frameOk :=
  fun h =>
    ay_mcrb_batch_evidence_frame
      (ay_mcrb_refined_batch_claim_evidence h)

theorem ay_mcrb_claim_requires_projection
    {refinementMapOk coreGuidanceOk childCoverageOk frameOk projectionOk
      replayOk auditEntry publicResult : Prop} :
    AyMCRBRefinedBatchClaim
      (AyMCRBBatchEvidence
        refinementMapOk coreGuidanceOk childCoverageOk frameOk
        projectionOk replayOk)
      auditEntry
      publicResult ->
    projectionOk :=
  fun h =>
    ay_mcrb_batch_evidence_projection
      (ay_mcrb_refined_batch_claim_evidence h)

theorem ay_mcrb_claim_requires_checker_replay
    {refinementMapOk coreGuidanceOk childCoverageOk frameOk projectionOk
      replayOk auditEntry publicResult : Prop} :
    AyMCRBRefinedBatchClaim
      (AyMCRBBatchEvidence
        refinementMapOk coreGuidanceOk childCoverageOk frameOk
        projectionOk replayOk)
      auditEntry
      publicResult ->
    replayOk :=
  fun h =>
    ay_mcrb_batch_evidence_replay
      (ay_mcrb_refined_batch_claim_evidence h)

theorem ay_mcrb_refined_batch_claim_sound_exact
    {batchEvidence auditEntry publicResult : Prop} :
    AyMCRBEquisat
      (AyMCRBRefinedBatchClaim batchEvidence auditEntry publicResult)
      (AyMCRBConj batchEvidence (AyMCRBConj auditEntry publicResult)) :=
  ay_mcrb_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_mcrb_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMCRBNoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_mcrb_conj_intro hdiagnostic hblocks

theorem ay_mcrb_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMCRBNoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_mcrb_conj_left h

theorem ay_mcrb_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMCRBNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_mcrb_conj_right h

theorem ay_mcrb_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMCRBRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_mcrb_conj_intro hreason hrequest

theorem ay_mcrb_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMCRBRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_mcrb_conj_left h

theorem ay_mcrb_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMCRBRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_mcrb_conj_right h

theorem ay_mcrb_stale_refinement_recompute
    {staleRefinement recomputeRequest : Prop} :
    staleRefinement ->
    recomputeRequest ->
    AyMCRBRecomputeObligation staleRefinement recomputeRequest :=
  fun hstale hrecompute =>
    ay_mcrb_recompute_obligation_intro hstale hrecompute

theorem ay_mcrb_stale_refinement_no_claim
    {staleRefinement publicClaim : Prop} :
    staleRefinement ->
    (staleRefinement -> publicClaim -> False) ->
    AyMCRBNoClaimDiagnostic staleRefinement publicClaim :=
  fun hstale hblocks =>
    ay_mcrb_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_mcrb_uncovered_refinement_no_claim
    {uncoveredRefinement publicClaim : Prop} :
    uncoveredRefinement ->
    (uncoveredRefinement -> publicClaim -> False) ->
    AyMCRBNoClaimDiagnostic uncoveredRefinement publicClaim :=
  fun huncovered hblocks =>
    ay_mcrb_no_claim_diagnostic_intro huncovered (hblocks huncovered)

theorem ay_mcrb_refinement_map_mismatch_no_claim
    {refinementMapMismatch publicClaim : Prop} :
    refinementMapMismatch ->
    (refinementMapMismatch -> publicClaim -> False) ->
    AyMCRBNoClaimDiagnostic refinementMapMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mcrb_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mcrb_parent_frame_mismatch_no_claim
    {parentFrameMismatch publicClaim : Prop} :
    parentFrameMismatch ->
    (parentFrameMismatch -> publicClaim -> False) ->
    AyMCRBNoClaimDiagnostic parentFrameMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mcrb_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mcrb_projection_reconstruction_mismatch_no_claim
    {projectionReconstructionMismatch publicClaim : Prop} :
    projectionReconstructionMismatch ->
    (projectionReconstructionMismatch -> publicClaim -> False) ->
    AyMCRBNoClaimDiagnostic projectionReconstructionMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mcrb_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mcrb_checker_replay_reject_no_claim
    {checkerReplayReject publicClaim : Prop} :
    checkerReplayReject ->
    (checkerReplayReject -> publicClaim -> False) ->
    AyMCRBNoClaimDiagnostic checkerReplayReject publicClaim :=
  fun hreject hblocks =>
    ay_mcrb_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_mcrb_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMCRBNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_mcrb_no_claim_diagnostic_blocks h hclaim

theorem ay_mcrb_bad_batch_refinement_no_stale_public_result
    {staleRefinement uncoveredRefinement refinementMapMismatch
      parentFrameMismatch projectionReconstructionMismatch checkerReplayReject
      publicClaim : Prop} :
    (staleRefinement -> publicClaim -> False) ->
    (uncoveredRefinement -> publicClaim -> False) ->
    (refinementMapMismatch -> publicClaim -> False) ->
    (parentFrameMismatch -> publicClaim -> False) ->
    (projectionReconstructionMismatch -> publicClaim -> False) ->
    (checkerReplayReject -> publicClaim -> False) ->
    AyMCRBConj
      (staleRefinement ->
        AyMCRBNoClaimDiagnostic staleRefinement publicClaim)
      (AyMCRBConj
        (uncoveredRefinement ->
          AyMCRBNoClaimDiagnostic uncoveredRefinement publicClaim)
        (AyMCRBConj
          (refinementMapMismatch ->
            AyMCRBNoClaimDiagnostic refinementMapMismatch publicClaim)
          (AyMCRBConj
            (parentFrameMismatch ->
              AyMCRBNoClaimDiagnostic parentFrameMismatch publicClaim)
            (AyMCRBConj
              (projectionReconstructionMismatch ->
                AyMCRBNoClaimDiagnostic
                  projectionReconstructionMismatch publicClaim)
              (checkerReplayReject ->
                AyMCRBNoClaimDiagnostic
                  checkerReplayReject publicClaim))))) :=
  fun hstale huncovered hmap hframe hprojection hreplay =>
    ay_mcrb_conj_intro
      (fun h => ay_mcrb_stale_refinement_no_claim h hstale)
      (ay_mcrb_conj_intro
        (fun h => ay_mcrb_uncovered_refinement_no_claim h huncovered)
        (ay_mcrb_conj_intro
          (fun h => ay_mcrb_refinement_map_mismatch_no_claim h hmap)
          (ay_mcrb_conj_intro
            (fun h => ay_mcrb_parent_frame_mismatch_no_claim h hframe)
            (ay_mcrb_conj_intro
              (fun h =>
                ay_mcrb_projection_reconstruction_mismatch_no_claim
                  h hprojection)
              (fun h => ay_mcrb_checker_replay_reject_no_claim h hreplay)))))
