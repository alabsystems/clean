-- SAT-COMP/ay assumption-core extraction model/proof gating skeleton.
-- The predicates describe when an extracted cube/incremental assumption core
-- may guide later SAT/UNSAT work without becoming a stale public-result claim.

def AyMACEConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMACEDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMACEEquisat (left right : Prop) : Prop :=
  AyMACEConj (left -> right) (right -> left)

def AyMACEAssumptionCore
    (coreMembership frameIdentity minimizationWitness : Prop) : Prop :=
  AyMACEConj coreMembership (AyMACEConj frameIdentity minimizationWitness)

def AyMACEProjectionReconstruction
    (projectionEvidence reconstructionEvidence : Prop) : Prop :=
  AyMACEConj projectionEvidence reconstructionEvidence

def AyMACECheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMACEConj checkerAccepted replayTrace

def AyMACEPublicResultEvidence
    (satEvidence unsatEvidence resultSelector : Prop) : Prop :=
  AyMACEConj resultSelector (AyMACEConj satEvidence unsatEvidence)

def AyMACECoreGuidanceEvidence
    (coreOk frameOk projectionOk replayOk publicResultOk : Prop) : Prop :=
  AyMACEConj coreOk
    (AyMACEConj frameOk
      (AyMACEConj projectionOk
        (AyMACEConj replayOk publicResultOk)))

def AyMACEGuidedWorkClaim
    (guidanceEvidence auditEntry publicResult : Prop) : Prop :=
  AyMACEConj guidanceEvidence (AyMACEConj auditEntry publicResult)

def AyMACENoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMACEConj diagnostic (publicClaim -> False)

def AyMACERecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMACEConj reason recomputeRequest

theorem ay_mace_conj_intro {left right : Prop} :
    left -> right -> AyMACEConj left right :=
  fun hleft hright goal k => k hleft hright

theorem ay_mace_conj_left {left right : Prop} :
    AyMACEConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mace_conj_right {left right : Prop} :
    AyMACEConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mace_disj_left {left right : Prop} :
    left -> AyMACEDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mace_disj_right {left right : Prop} :
    right -> AyMACEDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mace_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMACEEquisat left right :=
  fun hf hb => ay_mace_conj_intro hf hb

theorem ay_mace_equisat_forward {left right : Prop} :
    AyMACEEquisat left right -> left -> right :=
  fun h => ay_mace_conj_left h

theorem ay_mace_equisat_backward {left right : Prop} :
    AyMACEEquisat left right -> right -> left :=
  fun h => ay_mace_conj_right h

theorem ay_mace_assumption_core_intro
    {coreMembership frameIdentity minimizationWitness : Prop} :
    coreMembership ->
    frameIdentity ->
    minimizationWitness ->
    AyMACEAssumptionCore coreMembership frameIdentity minimizationWitness :=
  fun hcore hframe hmin =>
    ay_mace_conj_intro hcore (ay_mace_conj_intro hframe hmin)

theorem ay_mace_assumption_core_membership
    {coreMembership frameIdentity minimizationWitness : Prop} :
    AyMACEAssumptionCore coreMembership frameIdentity minimizationWitness ->
    coreMembership :=
  fun h => ay_mace_conj_left h

theorem ay_mace_assumption_core_frame
    {coreMembership frameIdentity minimizationWitness : Prop} :
    AyMACEAssumptionCore coreMembership frameIdentity minimizationWitness ->
    frameIdentity :=
  fun h => ay_mace_conj_left (ay_mace_conj_right h)

theorem ay_mace_assumption_core_minimization
    {coreMembership frameIdentity minimizationWitness : Prop} :
    AyMACEAssumptionCore coreMembership frameIdentity minimizationWitness ->
    minimizationWitness :=
  fun h => ay_mace_conj_right (ay_mace_conj_right h)

theorem ay_mace_projection_reconstruction_intro
    {projectionEvidence reconstructionEvidence : Prop} :
    projectionEvidence ->
    reconstructionEvidence ->
    AyMACEProjectionReconstruction projectionEvidence reconstructionEvidence :=
  fun hprojection hreconstruction =>
    ay_mace_conj_intro hprojection hreconstruction

theorem ay_mace_projection_reconstruction_projection
    {projectionEvidence reconstructionEvidence : Prop} :
    AyMACEProjectionReconstruction projectionEvidence reconstructionEvidence ->
    projectionEvidence :=
  fun h => ay_mace_conj_left h

theorem ay_mace_projection_reconstruction_reconstruction
    {projectionEvidence reconstructionEvidence : Prop} :
    AyMACEProjectionReconstruction projectionEvidence reconstructionEvidence ->
    reconstructionEvidence :=
  fun h => ay_mace_conj_right h

theorem ay_mace_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMACECheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mace_conj_intro haccepted htrace

theorem ay_mace_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMACECheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_mace_conj_left h

theorem ay_mace_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMACECheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_mace_conj_right h

theorem ay_mace_public_result_evidence_intro
    {satEvidence unsatEvidence resultSelector : Prop} :
    resultSelector ->
    satEvidence ->
    unsatEvidence ->
    AyMACEPublicResultEvidence satEvidence unsatEvidence resultSelector :=
  fun hselector hsat hunsat =>
    ay_mace_conj_intro hselector (ay_mace_conj_intro hsat hunsat)

theorem ay_mace_public_result_evidence_selector
    {satEvidence unsatEvidence resultSelector : Prop} :
    AyMACEPublicResultEvidence satEvidence unsatEvidence resultSelector ->
    resultSelector :=
  fun h => ay_mace_conj_left h

theorem ay_mace_public_result_evidence_sat
    {satEvidence unsatEvidence resultSelector : Prop} :
    AyMACEPublicResultEvidence satEvidence unsatEvidence resultSelector ->
    satEvidence :=
  fun h => ay_mace_conj_left (ay_mace_conj_right h)

theorem ay_mace_public_result_evidence_unsat
    {satEvidence unsatEvidence resultSelector : Prop} :
    AyMACEPublicResultEvidence satEvidence unsatEvidence resultSelector ->
    unsatEvidence :=
  fun h => ay_mace_conj_right (ay_mace_conj_right h)

theorem ay_mace_core_guidance_evidence_intro
    {coreOk frameOk projectionOk replayOk publicResultOk : Prop} :
    coreOk ->
    frameOk ->
    projectionOk ->
    replayOk ->
    publicResultOk ->
    AyMACECoreGuidanceEvidence
      coreOk frameOk projectionOk replayOk publicResultOk :=
  fun hcore hframe hprojection hreplay hresult =>
    ay_mace_conj_intro hcore
      (ay_mace_conj_intro hframe
        (ay_mace_conj_intro hprojection
          (ay_mace_conj_intro hreplay hresult)))

theorem ay_mace_core_guidance_evidence_core
    {coreOk frameOk projectionOk replayOk publicResultOk : Prop} :
    AyMACECoreGuidanceEvidence
      coreOk frameOk projectionOk replayOk publicResultOk ->
    coreOk :=
  fun h => ay_mace_conj_left h

theorem ay_mace_core_guidance_evidence_frame
    {coreOk frameOk projectionOk replayOk publicResultOk : Prop} :
    AyMACECoreGuidanceEvidence
      coreOk frameOk projectionOk replayOk publicResultOk ->
    frameOk :=
  fun h => ay_mace_conj_left (ay_mace_conj_right h)

theorem ay_mace_core_guidance_evidence_projection
    {coreOk frameOk projectionOk replayOk publicResultOk : Prop} :
    AyMACECoreGuidanceEvidence
      coreOk frameOk projectionOk replayOk publicResultOk ->
    projectionOk :=
  fun h => ay_mace_conj_left (ay_mace_conj_right (ay_mace_conj_right h))

theorem ay_mace_core_guidance_evidence_replay
    {coreOk frameOk projectionOk replayOk publicResultOk : Prop} :
    AyMACECoreGuidanceEvidence
      coreOk frameOk projectionOk replayOk publicResultOk ->
    replayOk :=
  fun h =>
    ay_mace_conj_left
      (ay_mace_conj_right (ay_mace_conj_right (ay_mace_conj_right h)))

theorem ay_mace_core_guidance_evidence_public_result
    {coreOk frameOk projectionOk replayOk publicResultOk : Prop} :
    AyMACECoreGuidanceEvidence
      coreOk frameOk projectionOk replayOk publicResultOk ->
    publicResultOk :=
  fun h =>
    ay_mace_conj_right
      (ay_mace_conj_right (ay_mace_conj_right (ay_mace_conj_right h)))

theorem ay_mace_guided_work_claim_intro
    {guidanceEvidence auditEntry publicResult : Prop} :
    guidanceEvidence ->
    auditEntry ->
    publicResult ->
    AyMACEGuidedWorkClaim guidanceEvidence auditEntry publicResult :=
  fun hevidence haudit hresult =>
    ay_mace_conj_intro hevidence (ay_mace_conj_intro haudit hresult)

theorem ay_mace_guided_work_claim_evidence
    {guidanceEvidence auditEntry publicResult : Prop} :
    AyMACEGuidedWorkClaim guidanceEvidence auditEntry publicResult ->
    guidanceEvidence :=
  fun h => ay_mace_conj_left h

theorem ay_mace_guided_work_claim_audit
    {guidanceEvidence auditEntry publicResult : Prop} :
    AyMACEGuidedWorkClaim guidanceEvidence auditEntry publicResult ->
    auditEntry :=
  fun h => ay_mace_conj_left (ay_mace_conj_right h)

theorem ay_mace_guided_work_claim_result
    {guidanceEvidence auditEntry publicResult : Prop} :
    AyMACEGuidedWorkClaim guidanceEvidence auditEntry publicResult ->
    publicResult :=
  fun h => ay_mace_conj_right (ay_mace_conj_right h)

theorem ay_mace_guided_work_requires_core
    {coreOk frameOk projectionOk replayOk publicResultOk auditEntry
      publicResult : Prop} :
    AyMACEGuidedWorkClaim
      (AyMACECoreGuidanceEvidence
        coreOk frameOk projectionOk replayOk publicResultOk)
      auditEntry
      publicResult ->
    coreOk :=
  fun h =>
    ay_mace_core_guidance_evidence_core
      (ay_mace_guided_work_claim_evidence h)

theorem ay_mace_guided_work_requires_frame
    {coreOk frameOk projectionOk replayOk publicResultOk auditEntry
      publicResult : Prop} :
    AyMACEGuidedWorkClaim
      (AyMACECoreGuidanceEvidence
        coreOk frameOk projectionOk replayOk publicResultOk)
      auditEntry
      publicResult ->
    frameOk :=
  fun h =>
    ay_mace_core_guidance_evidence_frame
      (ay_mace_guided_work_claim_evidence h)

theorem ay_mace_guided_work_requires_projection
    {coreOk frameOk projectionOk replayOk publicResultOk auditEntry
      publicResult : Prop} :
    AyMACEGuidedWorkClaim
      (AyMACECoreGuidanceEvidence
        coreOk frameOk projectionOk replayOk publicResultOk)
      auditEntry
      publicResult ->
    projectionOk :=
  fun h =>
    ay_mace_core_guidance_evidence_projection
      (ay_mace_guided_work_claim_evidence h)

theorem ay_mace_guided_work_requires_replay
    {coreOk frameOk projectionOk replayOk publicResultOk auditEntry
      publicResult : Prop} :
    AyMACEGuidedWorkClaim
      (AyMACECoreGuidanceEvidence
        coreOk frameOk projectionOk replayOk publicResultOk)
      auditEntry
      publicResult ->
    replayOk :=
  fun h =>
    ay_mace_core_guidance_evidence_replay
      (ay_mace_guided_work_claim_evidence h)

theorem ay_mace_guided_work_requires_public_result
    {coreOk frameOk projectionOk replayOk publicResultOk auditEntry
      publicResult : Prop} :
    AyMACEGuidedWorkClaim
      (AyMACECoreGuidanceEvidence
        coreOk frameOk projectionOk replayOk publicResultOk)
      auditEntry
      publicResult ->
    publicResultOk :=
  fun h =>
    ay_mace_core_guidance_evidence_public_result
      (ay_mace_guided_work_claim_evidence h)

theorem ay_mace_guided_work_sound_exact
    {guidanceEvidence auditEntry publicResult : Prop} :
    AyMACEEquisat
      (AyMACEGuidedWorkClaim guidanceEvidence auditEntry publicResult)
      (AyMACEConj guidanceEvidence (AyMACEConj auditEntry publicResult)) :=
  ay_mace_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_mace_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMACENoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_mace_conj_intro hdiagnostic hblocks

theorem ay_mace_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMACENoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_mace_conj_left h

theorem ay_mace_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMACENoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_mace_conj_right h

theorem ay_mace_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMACERecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_mace_conj_intro hreason hrequest

theorem ay_mace_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMACERecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_mace_conj_left h

theorem ay_mace_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMACERecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_mace_conj_right h

theorem ay_mace_stale_core_recompute
    {staleCore recomputeRequest : Prop} :
    staleCore ->
    recomputeRequest ->
    AyMACERecomputeObligation staleCore recomputeRequest :=
  fun hstale hrecompute =>
    ay_mace_recompute_obligation_intro hstale hrecompute

theorem ay_mace_stale_core_no_claim
    {staleCore publicClaim : Prop} :
    staleCore ->
    (staleCore -> publicClaim -> False) ->
    AyMACENoClaimDiagnostic staleCore publicClaim :=
  fun hstale hblocks =>
    ay_mace_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_mace_over_minimized_core_no_claim
    {overMinimizedCore publicClaim : Prop} :
    overMinimizedCore ->
    (overMinimizedCore -> publicClaim -> False) ->
    AyMACENoClaimDiagnostic overMinimizedCore publicClaim :=
  fun hover hblocks =>
    ay_mace_no_claim_diagnostic_intro hover (hblocks hover)

theorem ay_mace_frame_mismatch_no_claim
    {frameMismatch publicClaim : Prop} :
    frameMismatch ->
    (frameMismatch -> publicClaim -> False) ->
    AyMACENoClaimDiagnostic frameMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mace_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mace_projection_reconstruction_mismatch_no_claim
    {projectionReconstructionMismatch publicClaim : Prop} :
    projectionReconstructionMismatch ->
    (projectionReconstructionMismatch -> publicClaim -> False) ->
    AyMACENoClaimDiagnostic projectionReconstructionMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mace_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mace_checker_replay_reject_no_claim
    {checkerReplayReject publicClaim : Prop} :
    checkerReplayReject ->
    (checkerReplayReject -> publicClaim -> False) ->
    AyMACENoClaimDiagnostic checkerReplayReject publicClaim :=
  fun hreject hblocks =>
    ay_mace_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_mace_public_result_mismatch_no_claim
    {publicResultMismatch publicClaim : Prop} :
    publicResultMismatch ->
    (publicResultMismatch -> publicClaim -> False) ->
    AyMACENoClaimDiagnostic publicResultMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mace_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mace_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMACENoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_mace_no_claim_diagnostic_blocks h hclaim

theorem ay_mace_bad_core_extraction_no_stale_public_result
    {staleCore overMinimizedCore frameMismatch projectionReconstructionMismatch
      checkerReplayReject publicResultMismatch publicClaim : Prop} :
    (staleCore -> publicClaim -> False) ->
    (overMinimizedCore -> publicClaim -> False) ->
    (frameMismatch -> publicClaim -> False) ->
    (projectionReconstructionMismatch -> publicClaim -> False) ->
    (checkerReplayReject -> publicClaim -> False) ->
    (publicResultMismatch -> publicClaim -> False) ->
    AyMACEConj
      (staleCore -> AyMACENoClaimDiagnostic staleCore publicClaim)
      (AyMACEConj
        (overMinimizedCore ->
          AyMACENoClaimDiagnostic overMinimizedCore publicClaim)
        (AyMACEConj
          (frameMismatch ->
            AyMACENoClaimDiagnostic frameMismatch publicClaim)
          (AyMACEConj
            (projectionReconstructionMismatch ->
              AyMACENoClaimDiagnostic
                projectionReconstructionMismatch publicClaim)
            (AyMACEConj
              (checkerReplayReject ->
                AyMACENoClaimDiagnostic checkerReplayReject publicClaim)
              (publicResultMismatch ->
                AyMACENoClaimDiagnostic
                  publicResultMismatch publicClaim))))) :=
  fun hstale hover hframe hprojection hreplay hresult =>
    ay_mace_conj_intro
      (fun h => ay_mace_stale_core_no_claim h hstale)
      (ay_mace_conj_intro
        (fun h => ay_mace_over_minimized_core_no_claim h hover)
        (ay_mace_conj_intro
          (fun h => ay_mace_frame_mismatch_no_claim h hframe)
          (ay_mace_conj_intro
            (fun h =>
              ay_mace_projection_reconstruction_mismatch_no_claim
                h hprojection)
            (ay_mace_conj_intro
              (fun h => ay_mace_checker_replay_reject_no_claim h hreplay)
              (fun h => ay_mace_public_result_mismatch_no_claim h hresult)))))
