-- SAT-COMP/ay multi-step refinement projection chain soundness skeleton.
-- Deeply refined SAT/UNSAT results may be projected to the original formula
-- only through a chain whose every edge carries the required evidence.

def AyMRPCConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMRPCDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMRPCEquisat (left right : Prop) : Prop :=
  AyMRPCConj (left -> right) (right -> left)

def AyMRPCEdgeCoverage
    (sourceCovered targetCovered targetImpliesSource : Prop) : Prop :=
  AyMRPCConj sourceCovered
    (AyMRPCConj targetCovered targetImpliesSource)

def AyMRPCProjectionReconstruction
    (projectionEvidence reconstructionEvidence : Prop) : Prop :=
  AyMRPCConj projectionEvidence reconstructionEvidence

def AyMRPCAssignmentCompatibility
    (targetAssignment sourceAssignment visibleAssignment : Prop) : Prop :=
  AyMRPCConj targetAssignment
    (AyMRPCConj sourceAssignment visibleAssignment)

def AyMRPCProofReconstruction
    (targetProof sourceProof visibleProof : Prop) : Prop :=
  AyMRPCConj targetProof (AyMRPCConj sourceProof visibleProof)

def AyMRPCFormulaFingerprint
    (targetFingerprint sourceFingerprint chainFingerprint : Prop) : Prop :=
  AyMRPCConj targetFingerprint
    (AyMRPCConj sourceFingerprint chainFingerprint)

def AyMRPCCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMRPCConj checkerAccepted replayTrace

def AyMRPCEdgeEvidence
    (coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk :
      Prop) : Prop :=
  AyMRPCConj coverageOk
    (AyMRPCConj projectionOk
      (AyMRPCConj assignmentOk
        (AyMRPCConj proofOk
          (AyMRPCConj fingerprintOk replayOk))))

def AyMRPCChainEvidence
    (headEdgeOk tailChainOk terminalResultOk : Prop) : Prop :=
  AyMRPCConj headEdgeOk (AyMRPCConj tailChainOk terminalResultOk)

def AyMRPCChainLiftedClaim
    (chainEvidence auditEntry publicResult : Prop) : Prop :=
  AyMRPCConj chainEvidence (AyMRPCConj auditEntry publicResult)

def AyMRPCNoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMRPCConj diagnostic (publicClaim -> False)

def AyMRPCRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMRPCConj reason recomputeRequest

theorem ay_mrpc_conj_intro {left right : Prop} :
    left -> right -> AyMRPCConj left right :=
  fun hleft hright goal k => k hleft hright

theorem ay_mrpc_conj_left {left right : Prop} :
    AyMRPCConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mrpc_conj_right {left right : Prop} :
    AyMRPCConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mrpc_disj_left {left right : Prop} :
    left -> AyMRPCDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mrpc_disj_right {left right : Prop} :
    right -> AyMRPCDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mrpc_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMRPCEquisat left right :=
  fun hf hb => ay_mrpc_conj_intro hf hb

theorem ay_mrpc_equisat_forward {left right : Prop} :
    AyMRPCEquisat left right -> left -> right :=
  fun h => ay_mrpc_conj_left h

theorem ay_mrpc_equisat_backward {left right : Prop} :
    AyMRPCEquisat left right -> right -> left :=
  fun h => ay_mrpc_conj_right h

theorem ay_mrpc_edge_coverage_intro
    {sourceCovered targetCovered targetImpliesSource : Prop} :
    sourceCovered ->
    targetCovered ->
    targetImpliesSource ->
    AyMRPCEdgeCoverage sourceCovered targetCovered targetImpliesSource :=
  fun hsource htarget himplies =>
    ay_mrpc_conj_intro hsource
      (ay_mrpc_conj_intro htarget himplies)

theorem ay_mrpc_edge_coverage_source
    {sourceCovered targetCovered targetImpliesSource : Prop} :
    AyMRPCEdgeCoverage sourceCovered targetCovered targetImpliesSource ->
    sourceCovered :=
  fun h => ay_mrpc_conj_left h

theorem ay_mrpc_edge_coverage_target
    {sourceCovered targetCovered targetImpliesSource : Prop} :
    AyMRPCEdgeCoverage sourceCovered targetCovered targetImpliesSource ->
    targetCovered :=
  fun h => ay_mrpc_conj_left (ay_mrpc_conj_right h)

theorem ay_mrpc_edge_coverage_target_implies_source
    {sourceCovered targetCovered targetImpliesSource : Prop} :
    AyMRPCEdgeCoverage sourceCovered targetCovered targetImpliesSource ->
    targetImpliesSource :=
  fun h => ay_mrpc_conj_right (ay_mrpc_conj_right h)

theorem ay_mrpc_projection_reconstruction_intro
    {projectionEvidence reconstructionEvidence : Prop} :
    projectionEvidence ->
    reconstructionEvidence ->
    AyMRPCProjectionReconstruction
      projectionEvidence reconstructionEvidence :=
  fun hprojection hreconstruction =>
    ay_mrpc_conj_intro hprojection hreconstruction

theorem ay_mrpc_projection_reconstruction_projection
    {projectionEvidence reconstructionEvidence : Prop} :
    AyMRPCProjectionReconstruction
      projectionEvidence reconstructionEvidence ->
    projectionEvidence :=
  fun h => ay_mrpc_conj_left h

theorem ay_mrpc_projection_reconstruction_reconstruction
    {projectionEvidence reconstructionEvidence : Prop} :
    AyMRPCProjectionReconstruction
      projectionEvidence reconstructionEvidence ->
    reconstructionEvidence :=
  fun h => ay_mrpc_conj_right h

theorem ay_mrpc_assignment_compatibility_intro
    {targetAssignment sourceAssignment visibleAssignment : Prop} :
    targetAssignment ->
    sourceAssignment ->
    visibleAssignment ->
    AyMRPCAssignmentCompatibility
      targetAssignment sourceAssignment visibleAssignment :=
  fun htarget hsource hvisible =>
    ay_mrpc_conj_intro htarget
      (ay_mrpc_conj_intro hsource hvisible)

theorem ay_mrpc_assignment_compatibility_target
    {targetAssignment sourceAssignment visibleAssignment : Prop} :
    AyMRPCAssignmentCompatibility
      targetAssignment sourceAssignment visibleAssignment ->
    targetAssignment :=
  fun h => ay_mrpc_conj_left h

theorem ay_mrpc_assignment_compatibility_source
    {targetAssignment sourceAssignment visibleAssignment : Prop} :
    AyMRPCAssignmentCompatibility
      targetAssignment sourceAssignment visibleAssignment ->
    sourceAssignment :=
  fun h => ay_mrpc_conj_left (ay_mrpc_conj_right h)

theorem ay_mrpc_assignment_compatibility_visible
    {targetAssignment sourceAssignment visibleAssignment : Prop} :
    AyMRPCAssignmentCompatibility
      targetAssignment sourceAssignment visibleAssignment ->
    visibleAssignment :=
  fun h => ay_mrpc_conj_right (ay_mrpc_conj_right h)

theorem ay_mrpc_proof_reconstruction_intro
    {targetProof sourceProof visibleProof : Prop} :
    targetProof ->
    sourceProof ->
    visibleProof ->
    AyMRPCProofReconstruction targetProof sourceProof visibleProof :=
  fun htarget hsource hvisible =>
    ay_mrpc_conj_intro htarget
      (ay_mrpc_conj_intro hsource hvisible)

theorem ay_mrpc_proof_reconstruction_target
    {targetProof sourceProof visibleProof : Prop} :
    AyMRPCProofReconstruction targetProof sourceProof visibleProof ->
    targetProof :=
  fun h => ay_mrpc_conj_left h

theorem ay_mrpc_proof_reconstruction_source
    {targetProof sourceProof visibleProof : Prop} :
    AyMRPCProofReconstruction targetProof sourceProof visibleProof ->
    sourceProof :=
  fun h => ay_mrpc_conj_left (ay_mrpc_conj_right h)

theorem ay_mrpc_proof_reconstruction_visible
    {targetProof sourceProof visibleProof : Prop} :
    AyMRPCProofReconstruction targetProof sourceProof visibleProof ->
    visibleProof :=
  fun h => ay_mrpc_conj_right (ay_mrpc_conj_right h)

theorem ay_mrpc_formula_fingerprint_intro
    {targetFingerprint sourceFingerprint chainFingerprint : Prop} :
    targetFingerprint ->
    sourceFingerprint ->
    chainFingerprint ->
    AyMRPCFormulaFingerprint
      targetFingerprint sourceFingerprint chainFingerprint :=
  fun htarget hsource hchain =>
    ay_mrpc_conj_intro htarget
      (ay_mrpc_conj_intro hsource hchain)

theorem ay_mrpc_formula_fingerprint_target
    {targetFingerprint sourceFingerprint chainFingerprint : Prop} :
    AyMRPCFormulaFingerprint
      targetFingerprint sourceFingerprint chainFingerprint ->
    targetFingerprint :=
  fun h => ay_mrpc_conj_left h

theorem ay_mrpc_formula_fingerprint_source
    {targetFingerprint sourceFingerprint chainFingerprint : Prop} :
    AyMRPCFormulaFingerprint
      targetFingerprint sourceFingerprint chainFingerprint ->
    sourceFingerprint :=
  fun h => ay_mrpc_conj_left (ay_mrpc_conj_right h)

theorem ay_mrpc_formula_fingerprint_chain
    {targetFingerprint sourceFingerprint chainFingerprint : Prop} :
    AyMRPCFormulaFingerprint
      targetFingerprint sourceFingerprint chainFingerprint ->
    chainFingerprint :=
  fun h => ay_mrpc_conj_right (ay_mrpc_conj_right h)

theorem ay_mrpc_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMRPCCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mrpc_conj_intro haccepted htrace

theorem ay_mrpc_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMRPCCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_mrpc_conj_left h

theorem ay_mrpc_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMRPCCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_mrpc_conj_right h

theorem ay_mrpc_edge_evidence_intro
    {coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk :
      Prop} :
    coverageOk ->
    projectionOk ->
    assignmentOk ->
    proofOk ->
    fingerprintOk ->
    replayOk ->
    AyMRPCEdgeEvidence
      coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk :=
  fun hcoverage hprojection hassignment hproof hfingerprint hreplay =>
    ay_mrpc_conj_intro hcoverage
      (ay_mrpc_conj_intro hprojection
        (ay_mrpc_conj_intro hassignment
          (ay_mrpc_conj_intro hproof
            (ay_mrpc_conj_intro hfingerprint hreplay))))

theorem ay_mrpc_edge_evidence_coverage
    {coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk :
      Prop} :
    AyMRPCEdgeEvidence
      coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk ->
    coverageOk :=
  fun h => ay_mrpc_conj_left h

theorem ay_mrpc_edge_evidence_projection
    {coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk :
      Prop} :
    AyMRPCEdgeEvidence
      coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk ->
    projectionOk :=
  fun h => ay_mrpc_conj_left (ay_mrpc_conj_right h)

theorem ay_mrpc_edge_evidence_assignment
    {coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk :
      Prop} :
    AyMRPCEdgeEvidence
      coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk ->
    assignmentOk :=
  fun h => ay_mrpc_conj_left (ay_mrpc_conj_right (ay_mrpc_conj_right h))

theorem ay_mrpc_edge_evidence_proof
    {coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk :
      Prop} :
    AyMRPCEdgeEvidence
      coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk ->
    proofOk :=
  fun h =>
    ay_mrpc_conj_left
      (ay_mrpc_conj_right (ay_mrpc_conj_right (ay_mrpc_conj_right h)))

theorem ay_mrpc_edge_evidence_fingerprint
    {coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk :
      Prop} :
    AyMRPCEdgeEvidence
      coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk ->
    fingerprintOk :=
  fun h =>
    ay_mrpc_conj_left
      (ay_mrpc_conj_right
        (ay_mrpc_conj_right (ay_mrpc_conj_right (ay_mrpc_conj_right h))))

theorem ay_mrpc_edge_evidence_replay
    {coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk :
      Prop} :
    AyMRPCEdgeEvidence
      coverageOk projectionOk assignmentOk proofOk fingerprintOk replayOk ->
    replayOk :=
  fun h =>
    ay_mrpc_conj_right
      (ay_mrpc_conj_right
        (ay_mrpc_conj_right (ay_mrpc_conj_right (ay_mrpc_conj_right h))))

theorem ay_mrpc_chain_evidence_intro
    {headEdgeOk tailChainOk terminalResultOk : Prop} :
    headEdgeOk ->
    tailChainOk ->
    terminalResultOk ->
    AyMRPCChainEvidence headEdgeOk tailChainOk terminalResultOk :=
  fun hhead htail hterminal =>
    ay_mrpc_conj_intro hhead (ay_mrpc_conj_intro htail hterminal)

theorem ay_mrpc_chain_evidence_head
    {headEdgeOk tailChainOk terminalResultOk : Prop} :
    AyMRPCChainEvidence headEdgeOk tailChainOk terminalResultOk ->
    headEdgeOk :=
  fun h => ay_mrpc_conj_left h

theorem ay_mrpc_chain_evidence_tail
    {headEdgeOk tailChainOk terminalResultOk : Prop} :
    AyMRPCChainEvidence headEdgeOk tailChainOk terminalResultOk ->
    tailChainOk :=
  fun h => ay_mrpc_conj_left (ay_mrpc_conj_right h)

theorem ay_mrpc_chain_evidence_terminal
    {headEdgeOk tailChainOk terminalResultOk : Prop} :
    AyMRPCChainEvidence headEdgeOk tailChainOk terminalResultOk ->
    terminalResultOk :=
  fun h => ay_mrpc_conj_right (ay_mrpc_conj_right h)

theorem ay_mrpc_chain_compose
    {headEdgeOk tailChainOk terminalResultOk : Prop} :
    headEdgeOk ->
    AyMRPCChainEvidence tailChainOk terminalResultOk terminalResultOk ->
    AyMRPCChainEvidence headEdgeOk tailChainOk terminalResultOk :=
  fun hhead htail =>
    ay_mrpc_chain_evidence_intro hhead
      (ay_mrpc_chain_evidence_head htail)
      (ay_mrpc_chain_evidence_terminal htail)

theorem ay_mrpc_chain_lifted_claim_intro
    {chainEvidence auditEntry publicResult : Prop} :
    chainEvidence ->
    auditEntry ->
    publicResult ->
    AyMRPCChainLiftedClaim chainEvidence auditEntry publicResult :=
  fun hevidence haudit hresult =>
    ay_mrpc_conj_intro hevidence (ay_mrpc_conj_intro haudit hresult)

theorem ay_mrpc_chain_lifted_claim_evidence
    {chainEvidence auditEntry publicResult : Prop} :
    AyMRPCChainLiftedClaim chainEvidence auditEntry publicResult ->
    chainEvidence :=
  fun h => ay_mrpc_conj_left h

theorem ay_mrpc_chain_lifted_claim_audit
    {chainEvidence auditEntry publicResult : Prop} :
    AyMRPCChainLiftedClaim chainEvidence auditEntry publicResult ->
    auditEntry :=
  fun h => ay_mrpc_conj_left (ay_mrpc_conj_right h)

theorem ay_mrpc_chain_lifted_claim_result
    {chainEvidence auditEntry publicResult : Prop} :
    AyMRPCChainLiftedClaim chainEvidence auditEntry publicResult ->
    publicResult :=
  fun h => ay_mrpc_conj_right (ay_mrpc_conj_right h)

theorem ay_mrpc_accepted_chain_preserves_sat_claim
    {chainEvidence auditEntry publicSatClaim : Prop} :
    AyMRPCChainLiftedClaim chainEvidence auditEntry publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mrpc_chain_lifted_claim_result h

theorem ay_mrpc_accepted_chain_preserves_unsat_claim
    {chainEvidence auditEntry publicUnsatClaim : Prop} :
    AyMRPCChainLiftedClaim chainEvidence auditEntry publicUnsatClaim ->
    publicUnsatClaim :=
  fun h => ay_mrpc_chain_lifted_claim_result h

theorem ay_mrpc_chain_lifted_claim_sound_exact
    {chainEvidence auditEntry publicResult : Prop} :
    AyMRPCEquisat
      (AyMRPCChainLiftedClaim chainEvidence auditEntry publicResult)
      (AyMRPCConj chainEvidence (AyMRPCConj auditEntry publicResult)) :=
  ay_mrpc_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_mrpc_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMRPCNoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_mrpc_conj_intro hdiagnostic hblocks

theorem ay_mrpc_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMRPCNoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_mrpc_conj_left h

theorem ay_mrpc_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMRPCNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_mrpc_conj_right h

theorem ay_mrpc_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMRPCRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_mrpc_conj_intro hreason hrequest

theorem ay_mrpc_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMRPCRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_mrpc_conj_left h

theorem ay_mrpc_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMRPCRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_mrpc_conj_right h

theorem ay_mrpc_broken_edge_recompute
    {brokenEdge recomputeRequest : Prop} :
    brokenEdge ->
    recomputeRequest ->
    AyMRPCRecomputeObligation brokenEdge recomputeRequest :=
  fun hbroken hrecompute =>
    ay_mrpc_recompute_obligation_intro hbroken hrecompute

theorem ay_mrpc_broken_edge_no_claim
    {brokenEdge publicClaim : Prop} :
    brokenEdge ->
    (brokenEdge -> publicClaim -> False) ->
    AyMRPCNoClaimDiagnostic brokenEdge publicClaim :=
  fun hbroken hblocks =>
    ay_mrpc_no_claim_diagnostic_intro hbroken (hblocks hbroken)

theorem ay_mrpc_stale_fingerprint_no_claim
    {staleFingerprint publicClaim : Prop} :
    staleFingerprint ->
    (staleFingerprint -> publicClaim -> False) ->
    AyMRPCNoClaimDiagnostic staleFingerprint publicClaim :=
  fun hstale hblocks =>
    ay_mrpc_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_mrpc_projection_mismatch_no_claim
    {projectionMismatch publicClaim : Prop} :
    projectionMismatch ->
    (projectionMismatch -> publicClaim -> False) ->
    AyMRPCNoClaimDiagnostic projectionMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mrpc_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mrpc_assignment_mismatch_no_claim
    {assignmentMismatch publicClaim : Prop} :
    assignmentMismatch ->
    (assignmentMismatch -> publicClaim -> False) ->
    AyMRPCNoClaimDiagnostic assignmentMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mrpc_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mrpc_proof_reconstruction_mismatch_no_claim
    {proofReconstructionMismatch publicClaim : Prop} :
    proofReconstructionMismatch ->
    (proofReconstructionMismatch -> publicClaim -> False) ->
    AyMRPCNoClaimDiagnostic proofReconstructionMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mrpc_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mrpc_replay_rejection_no_claim
    {replayRejection publicClaim : Prop} :
    replayRejection ->
    (replayRejection -> publicClaim -> False) ->
    AyMRPCNoClaimDiagnostic replayRejection publicClaim :=
  fun hreject hblocks =>
    ay_mrpc_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_mrpc_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMRPCNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_mrpc_no_claim_diagnostic_blocks h hclaim

theorem ay_mrpc_bad_chain_no_stale_public_result
    {brokenEdge staleFingerprint projectionMismatch assignmentMismatch
      proofReconstructionMismatch replayRejection publicClaim : Prop} :
    (brokenEdge -> publicClaim -> False) ->
    (staleFingerprint -> publicClaim -> False) ->
    (projectionMismatch -> publicClaim -> False) ->
    (assignmentMismatch -> publicClaim -> False) ->
    (proofReconstructionMismatch -> publicClaim -> False) ->
    (replayRejection -> publicClaim -> False) ->
    AyMRPCConj
      (brokenEdge -> AyMRPCNoClaimDiagnostic brokenEdge publicClaim)
      (AyMRPCConj
        (staleFingerprint ->
          AyMRPCNoClaimDiagnostic staleFingerprint publicClaim)
        (AyMRPCConj
          (projectionMismatch ->
            AyMRPCNoClaimDiagnostic projectionMismatch publicClaim)
          (AyMRPCConj
            (assignmentMismatch ->
              AyMRPCNoClaimDiagnostic assignmentMismatch publicClaim)
            (AyMRPCConj
              (proofReconstructionMismatch ->
                AyMRPCNoClaimDiagnostic
                  proofReconstructionMismatch publicClaim)
              (replayRejection ->
                AyMRPCNoClaimDiagnostic replayRejection publicClaim))))) :=
  fun hbroken hfingerprint hprojection hassignment hproof hreplay =>
    ay_mrpc_conj_intro
      (fun h => ay_mrpc_broken_edge_no_claim h hbroken)
      (ay_mrpc_conj_intro
        (fun h => ay_mrpc_stale_fingerprint_no_claim h hfingerprint)
        (ay_mrpc_conj_intro
          (fun h => ay_mrpc_projection_mismatch_no_claim h hprojection)
          (ay_mrpc_conj_intro
            (fun h => ay_mrpc_assignment_mismatch_no_claim h hassignment)
            (ay_mrpc_conj_intro
              (fun h =>
                ay_mrpc_proof_reconstruction_mismatch_no_claim h hproof)
              (fun h => ay_mrpc_replay_rejection_no_claim h hreplay)))))
