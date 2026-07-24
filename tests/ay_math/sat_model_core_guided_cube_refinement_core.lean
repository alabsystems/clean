-- SAT-COMP/ay core-guided cube refinement soundness skeleton.
-- Assumption cores may refine cube batches only when the core, coverage,
-- parent frame, reconstruction, replay, and public-result evidence agree.

def AyMCGCRConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMCGCRDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMCGCREquisat (left right : Prop) : Prop :=
  AyMCGCRConj (left -> right) (right -> left)

def AyMCGCRCoreMembership
    (coreMember coreExtracted coreNotOverMinimized : Prop) : Prop :=
  AyMCGCRConj coreMember
    (AyMCGCRConj coreExtracted coreNotOverMinimized)

def AyMCGCRCubeCoverage
    (parentCubeCovered refinedCubesCover uncoveredBlocked : Prop) : Prop :=
  AyMCGCRConj parentCubeCovered
    (AyMCGCRConj refinedCubesCover uncoveredBlocked)

def AyMCGCRParentFrame
    (parentFrameId assumptionFrameIdentity cubeBatchIdentity : Prop) : Prop :=
  AyMCGCRConj parentFrameId
    (AyMCGCRConj assumptionFrameIdentity cubeBatchIdentity)

def AyMCGCRProjectionReconstruction
    (projectionEvidence reconstructionEvidence : Prop) : Prop :=
  AyMCGCRConj projectionEvidence reconstructionEvidence

def AyMCGCRCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMCGCRConj checkerAccepted replayTrace

def AyMCGCRPublicResultEvidence
    (publicResultKind publicResultCertificate : Prop) : Prop :=
  AyMCGCRConj publicResultKind publicResultCertificate

def AyMCGCRRefinementEvidence
    (coreOk coverageOk frameOk projectionOk replayOk publicResultOk : Prop) :
    Prop :=
  AyMCGCRConj coreOk
    (AyMCGCRConj coverageOk
      (AyMCGCRConj frameOk
        (AyMCGCRConj projectionOk
          (AyMCGCRConj replayOk publicResultOk))))

def AyMCGCRRefinedCubeClaim
    (refinementEvidence auditEntry publicResult : Prop) : Prop :=
  AyMCGCRConj refinementEvidence (AyMCGCRConj auditEntry publicResult)

def AyMCGCRNoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMCGCRConj diagnostic (publicClaim -> False)

def AyMCGCRRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMCGCRConj reason recomputeRequest

theorem ay_mcgcr_conj_intro {left right : Prop} :
    left -> right -> AyMCGCRConj left right :=
  fun hleft hright goal k => k hleft hright

theorem ay_mcgcr_conj_left {left right : Prop} :
    AyMCGCRConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mcgcr_conj_right {left right : Prop} :
    AyMCGCRConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mcgcr_disj_left {left right : Prop} :
    left -> AyMCGCRDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mcgcr_disj_right {left right : Prop} :
    right -> AyMCGCRDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mcgcr_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMCGCREquisat left right :=
  fun hf hb => ay_mcgcr_conj_intro hf hb

theorem ay_mcgcr_equisat_forward {left right : Prop} :
    AyMCGCREquisat left right -> left -> right :=
  fun h => ay_mcgcr_conj_left h

theorem ay_mcgcr_equisat_backward {left right : Prop} :
    AyMCGCREquisat left right -> right -> left :=
  fun h => ay_mcgcr_conj_right h

theorem ay_mcgcr_core_membership_intro
    {coreMember coreExtracted coreNotOverMinimized : Prop} :
    coreMember ->
    coreExtracted ->
    coreNotOverMinimized ->
    AyMCGCRCoreMembership coreMember coreExtracted coreNotOverMinimized :=
  fun hmember hextracted hminimal =>
    ay_mcgcr_conj_intro hmember
      (ay_mcgcr_conj_intro hextracted hminimal)

theorem ay_mcgcr_core_membership_member
    {coreMember coreExtracted coreNotOverMinimized : Prop} :
    AyMCGCRCoreMembership coreMember coreExtracted coreNotOverMinimized ->
    coreMember :=
  fun h => ay_mcgcr_conj_left h

theorem ay_mcgcr_core_membership_extracted
    {coreMember coreExtracted coreNotOverMinimized : Prop} :
    AyMCGCRCoreMembership coreMember coreExtracted coreNotOverMinimized ->
    coreExtracted :=
  fun h => ay_mcgcr_conj_left (ay_mcgcr_conj_right h)

theorem ay_mcgcr_core_membership_not_over_minimized
    {coreMember coreExtracted coreNotOverMinimized : Prop} :
    AyMCGCRCoreMembership coreMember coreExtracted coreNotOverMinimized ->
    coreNotOverMinimized :=
  fun h => ay_mcgcr_conj_right (ay_mcgcr_conj_right h)

theorem ay_mcgcr_cube_coverage_intro
    {parentCubeCovered refinedCubesCover uncoveredBlocked : Prop} :
    parentCubeCovered ->
    refinedCubesCover ->
    uncoveredBlocked ->
    AyMCGCRCubeCoverage
      parentCubeCovered refinedCubesCover uncoveredBlocked :=
  fun hparent hrefined hblocked =>
    ay_mcgcr_conj_intro hparent
      (ay_mcgcr_conj_intro hrefined hblocked)

theorem ay_mcgcr_cube_coverage_parent
    {parentCubeCovered refinedCubesCover uncoveredBlocked : Prop} :
    AyMCGCRCubeCoverage
      parentCubeCovered refinedCubesCover uncoveredBlocked ->
    parentCubeCovered :=
  fun h => ay_mcgcr_conj_left h

theorem ay_mcgcr_cube_coverage_refined
    {parentCubeCovered refinedCubesCover uncoveredBlocked : Prop} :
    AyMCGCRCubeCoverage
      parentCubeCovered refinedCubesCover uncoveredBlocked ->
    refinedCubesCover :=
  fun h => ay_mcgcr_conj_left (ay_mcgcr_conj_right h)

theorem ay_mcgcr_cube_coverage_uncovered_blocked
    {parentCubeCovered refinedCubesCover uncoveredBlocked : Prop} :
    AyMCGCRCubeCoverage
      parentCubeCovered refinedCubesCover uncoveredBlocked ->
    uncoveredBlocked :=
  fun h => ay_mcgcr_conj_right (ay_mcgcr_conj_right h)

theorem ay_mcgcr_parent_frame_intro
    {parentFrameId assumptionFrameIdentity cubeBatchIdentity : Prop} :
    parentFrameId ->
    assumptionFrameIdentity ->
    cubeBatchIdentity ->
    AyMCGCRParentFrame
      parentFrameId assumptionFrameIdentity cubeBatchIdentity :=
  fun hparent hframe hbatch =>
    ay_mcgcr_conj_intro hparent
      (ay_mcgcr_conj_intro hframe hbatch)

theorem ay_mcgcr_parent_frame_id
    {parentFrameId assumptionFrameIdentity cubeBatchIdentity : Prop} :
    AyMCGCRParentFrame
      parentFrameId assumptionFrameIdentity cubeBatchIdentity ->
    parentFrameId :=
  fun h => ay_mcgcr_conj_left h

theorem ay_mcgcr_parent_frame_assumption
    {parentFrameId assumptionFrameIdentity cubeBatchIdentity : Prop} :
    AyMCGCRParentFrame
      parentFrameId assumptionFrameIdentity cubeBatchIdentity ->
    assumptionFrameIdentity :=
  fun h => ay_mcgcr_conj_left (ay_mcgcr_conj_right h)

theorem ay_mcgcr_parent_frame_batch
    {parentFrameId assumptionFrameIdentity cubeBatchIdentity : Prop} :
    AyMCGCRParentFrame
      parentFrameId assumptionFrameIdentity cubeBatchIdentity ->
    cubeBatchIdentity :=
  fun h => ay_mcgcr_conj_right (ay_mcgcr_conj_right h)

theorem ay_mcgcr_projection_reconstruction_intro
    {projectionEvidence reconstructionEvidence : Prop} :
    projectionEvidence ->
    reconstructionEvidence ->
    AyMCGCRProjectionReconstruction
      projectionEvidence reconstructionEvidence :=
  fun hprojection hreconstruction =>
    ay_mcgcr_conj_intro hprojection hreconstruction

theorem ay_mcgcr_projection_reconstruction_projection
    {projectionEvidence reconstructionEvidence : Prop} :
    AyMCGCRProjectionReconstruction
      projectionEvidence reconstructionEvidence ->
    projectionEvidence :=
  fun h => ay_mcgcr_conj_left h

theorem ay_mcgcr_projection_reconstruction_reconstruction
    {projectionEvidence reconstructionEvidence : Prop} :
    AyMCGCRProjectionReconstruction
      projectionEvidence reconstructionEvidence ->
    reconstructionEvidence :=
  fun h => ay_mcgcr_conj_right h

theorem ay_mcgcr_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMCGCRCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mcgcr_conj_intro haccepted htrace

theorem ay_mcgcr_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMCGCRCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_mcgcr_conj_left h

theorem ay_mcgcr_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMCGCRCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_mcgcr_conj_right h

theorem ay_mcgcr_public_result_evidence_intro
    {publicResultKind publicResultCertificate : Prop} :
    publicResultKind ->
    publicResultCertificate ->
    AyMCGCRPublicResultEvidence
      publicResultKind publicResultCertificate :=
  fun hkind hcertificate =>
    ay_mcgcr_conj_intro hkind hcertificate

theorem ay_mcgcr_public_result_evidence_kind
    {publicResultKind publicResultCertificate : Prop} :
    AyMCGCRPublicResultEvidence
      publicResultKind publicResultCertificate ->
    publicResultKind :=
  fun h => ay_mcgcr_conj_left h

theorem ay_mcgcr_public_result_evidence_certificate
    {publicResultKind publicResultCertificate : Prop} :
    AyMCGCRPublicResultEvidence
      publicResultKind publicResultCertificate ->
    publicResultCertificate :=
  fun h => ay_mcgcr_conj_right h

theorem ay_mcgcr_refinement_evidence_intro
    {coreOk coverageOk frameOk projectionOk replayOk publicResultOk : Prop} :
    coreOk ->
    coverageOk ->
    frameOk ->
    projectionOk ->
    replayOk ->
    publicResultOk ->
    AyMCGCRRefinementEvidence
      coreOk coverageOk frameOk projectionOk replayOk publicResultOk :=
  fun hcore hcoverage hframe hprojection hreplay hresult =>
    ay_mcgcr_conj_intro hcore
      (ay_mcgcr_conj_intro hcoverage
        (ay_mcgcr_conj_intro hframe
          (ay_mcgcr_conj_intro hprojection
            (ay_mcgcr_conj_intro hreplay hresult))))

theorem ay_mcgcr_refinement_evidence_core
    {coreOk coverageOk frameOk projectionOk replayOk publicResultOk : Prop} :
    AyMCGCRRefinementEvidence
      coreOk coverageOk frameOk projectionOk replayOk publicResultOk ->
    coreOk :=
  fun h => ay_mcgcr_conj_left h

theorem ay_mcgcr_refinement_evidence_coverage
    {coreOk coverageOk frameOk projectionOk replayOk publicResultOk : Prop} :
    AyMCGCRRefinementEvidence
      coreOk coverageOk frameOk projectionOk replayOk publicResultOk ->
    coverageOk :=
  fun h => ay_mcgcr_conj_left (ay_mcgcr_conj_right h)

theorem ay_mcgcr_refinement_evidence_frame
    {coreOk coverageOk frameOk projectionOk replayOk publicResultOk : Prop} :
    AyMCGCRRefinementEvidence
      coreOk coverageOk frameOk projectionOk replayOk publicResultOk ->
    frameOk :=
  fun h => ay_mcgcr_conj_left (ay_mcgcr_conj_right (ay_mcgcr_conj_right h))

theorem ay_mcgcr_refinement_evidence_projection
    {coreOk coverageOk frameOk projectionOk replayOk publicResultOk : Prop} :
    AyMCGCRRefinementEvidence
      coreOk coverageOk frameOk projectionOk replayOk publicResultOk ->
    projectionOk :=
  fun h =>
    ay_mcgcr_conj_left
      (ay_mcgcr_conj_right (ay_mcgcr_conj_right (ay_mcgcr_conj_right h)))

theorem ay_mcgcr_refinement_evidence_replay
    {coreOk coverageOk frameOk projectionOk replayOk publicResultOk : Prop} :
    AyMCGCRRefinementEvidence
      coreOk coverageOk frameOk projectionOk replayOk publicResultOk ->
    replayOk :=
  fun h =>
    ay_mcgcr_conj_left
      (ay_mcgcr_conj_right
        (ay_mcgcr_conj_right (ay_mcgcr_conj_right (ay_mcgcr_conj_right h))))

theorem ay_mcgcr_refinement_evidence_public_result
    {coreOk coverageOk frameOk projectionOk replayOk publicResultOk : Prop} :
    AyMCGCRRefinementEvidence
      coreOk coverageOk frameOk projectionOk replayOk publicResultOk ->
    publicResultOk :=
  fun h =>
    ay_mcgcr_conj_right
      (ay_mcgcr_conj_right
        (ay_mcgcr_conj_right (ay_mcgcr_conj_right (ay_mcgcr_conj_right h))))

theorem ay_mcgcr_refined_cube_claim_intro
    {refinementEvidence auditEntry publicResult : Prop} :
    refinementEvidence ->
    auditEntry ->
    publicResult ->
    AyMCGCRRefinedCubeClaim refinementEvidence auditEntry publicResult :=
  fun hevidence haudit hresult =>
    ay_mcgcr_conj_intro hevidence (ay_mcgcr_conj_intro haudit hresult)

theorem ay_mcgcr_refined_cube_claim_evidence
    {refinementEvidence auditEntry publicResult : Prop} :
    AyMCGCRRefinedCubeClaim refinementEvidence auditEntry publicResult ->
    refinementEvidence :=
  fun h => ay_mcgcr_conj_left h

theorem ay_mcgcr_refined_cube_claim_audit
    {refinementEvidence auditEntry publicResult : Prop} :
    AyMCGCRRefinedCubeClaim refinementEvidence auditEntry publicResult ->
    auditEntry :=
  fun h => ay_mcgcr_conj_left (ay_mcgcr_conj_right h)

theorem ay_mcgcr_refined_cube_claim_result
    {refinementEvidence auditEntry publicResult : Prop} :
    AyMCGCRRefinedCubeClaim refinementEvidence auditEntry publicResult ->
    publicResult :=
  fun h => ay_mcgcr_conj_right (ay_mcgcr_conj_right h)

theorem ay_mcgcr_claim_requires_core
    {coreOk coverageOk frameOk projectionOk replayOk publicResultOk auditEntry
      publicResult : Prop} :
    AyMCGCRRefinedCubeClaim
      (AyMCGCRRefinementEvidence
        coreOk coverageOk frameOk projectionOk replayOk publicResultOk)
      auditEntry
      publicResult ->
    coreOk :=
  fun h =>
    ay_mcgcr_refinement_evidence_core
      (ay_mcgcr_refined_cube_claim_evidence h)

theorem ay_mcgcr_claim_requires_coverage
    {coreOk coverageOk frameOk projectionOk replayOk publicResultOk auditEntry
      publicResult : Prop} :
    AyMCGCRRefinedCubeClaim
      (AyMCGCRRefinementEvidence
        coreOk coverageOk frameOk projectionOk replayOk publicResultOk)
      auditEntry
      publicResult ->
    coverageOk :=
  fun h =>
    ay_mcgcr_refinement_evidence_coverage
      (ay_mcgcr_refined_cube_claim_evidence h)

theorem ay_mcgcr_claim_requires_frame
    {coreOk coverageOk frameOk projectionOk replayOk publicResultOk auditEntry
      publicResult : Prop} :
    AyMCGCRRefinedCubeClaim
      (AyMCGCRRefinementEvidence
        coreOk coverageOk frameOk projectionOk replayOk publicResultOk)
      auditEntry
      publicResult ->
    frameOk :=
  fun h =>
    ay_mcgcr_refinement_evidence_frame
      (ay_mcgcr_refined_cube_claim_evidence h)

theorem ay_mcgcr_claim_requires_projection
    {coreOk coverageOk frameOk projectionOk replayOk publicResultOk auditEntry
      publicResult : Prop} :
    AyMCGCRRefinedCubeClaim
      (AyMCGCRRefinementEvidence
        coreOk coverageOk frameOk projectionOk replayOk publicResultOk)
      auditEntry
      publicResult ->
    projectionOk :=
  fun h =>
    ay_mcgcr_refinement_evidence_projection
      (ay_mcgcr_refined_cube_claim_evidence h)

theorem ay_mcgcr_claim_requires_replay
    {coreOk coverageOk frameOk projectionOk replayOk publicResultOk auditEntry
      publicResult : Prop} :
    AyMCGCRRefinedCubeClaim
      (AyMCGCRRefinementEvidence
        coreOk coverageOk frameOk projectionOk replayOk publicResultOk)
      auditEntry
      publicResult ->
    replayOk :=
  fun h =>
    ay_mcgcr_refinement_evidence_replay
      (ay_mcgcr_refined_cube_claim_evidence h)

theorem ay_mcgcr_claim_requires_public_result
    {coreOk coverageOk frameOk projectionOk replayOk publicResultOk auditEntry
      publicResult : Prop} :
    AyMCGCRRefinedCubeClaim
      (AyMCGCRRefinementEvidence
        coreOk coverageOk frameOk projectionOk replayOk publicResultOk)
      auditEntry
      publicResult ->
    publicResultOk :=
  fun h =>
    ay_mcgcr_refinement_evidence_public_result
      (ay_mcgcr_refined_cube_claim_evidence h)

theorem ay_mcgcr_refined_cube_claim_sound_exact
    {refinementEvidence auditEntry publicResult : Prop} :
    AyMCGCREquisat
      (AyMCGCRRefinedCubeClaim refinementEvidence auditEntry publicResult)
      (AyMCGCRConj refinementEvidence
        (AyMCGCRConj auditEntry publicResult)) :=
  ay_mcgcr_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_mcgcr_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMCGCRNoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_mcgcr_conj_intro hdiagnostic hblocks

theorem ay_mcgcr_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMCGCRNoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_mcgcr_conj_left h

theorem ay_mcgcr_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMCGCRNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_mcgcr_conj_right h

theorem ay_mcgcr_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMCGCRRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_mcgcr_conj_intro hreason hrequest

theorem ay_mcgcr_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMCGCRRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_mcgcr_conj_left h

theorem ay_mcgcr_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMCGCRRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_mcgcr_conj_right h

theorem ay_mcgcr_stale_core_guidance_recompute
    {staleCoreGuidance recomputeRequest : Prop} :
    staleCoreGuidance ->
    recomputeRequest ->
    AyMCGCRRecomputeObligation staleCoreGuidance recomputeRequest :=
  fun hstale hrecompute =>
    ay_mcgcr_recompute_obligation_intro hstale hrecompute

theorem ay_mcgcr_stale_core_guidance_no_claim
    {staleCoreGuidance publicClaim : Prop} :
    staleCoreGuidance ->
    (staleCoreGuidance -> publicClaim -> False) ->
    AyMCGCRNoClaimDiagnostic staleCoreGuidance publicClaim :=
  fun hstale hblocks =>
    ay_mcgcr_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_mcgcr_uncovered_refinement_no_claim
    {uncoveredRefinement publicClaim : Prop} :
    uncoveredRefinement ->
    (uncoveredRefinement -> publicClaim -> False) ->
    AyMCGCRNoClaimDiagnostic uncoveredRefinement publicClaim :=
  fun huncovered hblocks =>
    ay_mcgcr_no_claim_diagnostic_intro huncovered (hblocks huncovered)

theorem ay_mcgcr_parent_frame_mismatch_no_claim
    {parentFrameMismatch publicClaim : Prop} :
    parentFrameMismatch ->
    (parentFrameMismatch -> publicClaim -> False) ->
    AyMCGCRNoClaimDiagnostic parentFrameMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mcgcr_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mcgcr_projection_reconstruction_mismatch_no_claim
    {projectionReconstructionMismatch publicClaim : Prop} :
    projectionReconstructionMismatch ->
    (projectionReconstructionMismatch -> publicClaim -> False) ->
    AyMCGCRNoClaimDiagnostic projectionReconstructionMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mcgcr_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mcgcr_checker_replay_reject_no_claim
    {checkerReplayReject publicClaim : Prop} :
    checkerReplayReject ->
    (checkerReplayReject -> publicClaim -> False) ->
    AyMCGCRNoClaimDiagnostic checkerReplayReject publicClaim :=
  fun hreject hblocks =>
    ay_mcgcr_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_mcgcr_public_result_mismatch_no_claim
    {publicResultMismatch publicClaim : Prop} :
    publicResultMismatch ->
    (publicResultMismatch -> publicClaim -> False) ->
    AyMCGCRNoClaimDiagnostic publicResultMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mcgcr_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mcgcr_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMCGCRNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_mcgcr_no_claim_diagnostic_blocks h hclaim

theorem ay_mcgcr_bad_refinement_no_stale_public_result
    {staleCoreGuidance uncoveredRefinement parentFrameMismatch
      projectionReconstructionMismatch checkerReplayReject
      publicResultMismatch publicClaim : Prop} :
    (staleCoreGuidance -> publicClaim -> False) ->
    (uncoveredRefinement -> publicClaim -> False) ->
    (parentFrameMismatch -> publicClaim -> False) ->
    (projectionReconstructionMismatch -> publicClaim -> False) ->
    (checkerReplayReject -> publicClaim -> False) ->
    (publicResultMismatch -> publicClaim -> False) ->
    AyMCGCRConj
      (staleCoreGuidance ->
        AyMCGCRNoClaimDiagnostic staleCoreGuidance publicClaim)
      (AyMCGCRConj
        (uncoveredRefinement ->
          AyMCGCRNoClaimDiagnostic uncoveredRefinement publicClaim)
        (AyMCGCRConj
          (parentFrameMismatch ->
            AyMCGCRNoClaimDiagnostic parentFrameMismatch publicClaim)
          (AyMCGCRConj
            (projectionReconstructionMismatch ->
              AyMCGCRNoClaimDiagnostic
                projectionReconstructionMismatch publicClaim)
            (AyMCGCRConj
              (checkerReplayReject ->
                AyMCGCRNoClaimDiagnostic checkerReplayReject publicClaim)
              (publicResultMismatch ->
                AyMCGCRNoClaimDiagnostic
                  publicResultMismatch publicClaim))))) :=
  fun hstale huncovered hframe hprojection hreplay hresult =>
    ay_mcgcr_conj_intro
      (fun h => ay_mcgcr_stale_core_guidance_no_claim h hstale)
      (ay_mcgcr_conj_intro
        (fun h => ay_mcgcr_uncovered_refinement_no_claim h huncovered)
        (ay_mcgcr_conj_intro
          (fun h => ay_mcgcr_parent_frame_mismatch_no_claim h hframe)
          (ay_mcgcr_conj_intro
            (fun h =>
              ay_mcgcr_projection_reconstruction_mismatch_no_claim
                h hprojection)
            (ay_mcgcr_conj_intro
              (fun h => ay_mcgcr_checker_replay_reject_no_claim h hreplay)
              (fun h => ay_mcgcr_public_result_mismatch_no_claim h hresult)))))
