-- SAT-COMP/ay incremental assumption-frame result lift soundness skeleton.
-- Results produced under assumptions may be published for the original formula
-- only when frame lineage, activations, reconstruction, compatibility,
-- fingerprints, and checker replay all agree.

def AyMIALConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMIALDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMIALEquisat (left right : Prop) : Prop :=
  AyMIALConj (left -> right) (right -> left)

def AyMIALAssumptionFrameLineage
    (rootFrame currentFrame lineageWitness : Prop) : Prop :=
  AyMIALConj rootFrame (AyMIALConj currentFrame lineageWitness)

def AyMIALActivationMapping
    (activationLiterals activationMap noDroppedActivation : Prop) : Prop :=
  AyMIALConj activationLiterals
    (AyMIALConj activationMap noDroppedActivation)

def AyMIALProjectionReconstruction
    (projectionEvidence reconstructionEvidence : Prop) : Prop :=
  AyMIALConj projectionEvidence reconstructionEvidence

def AyMIALModelCompatibility
    (assumptionModel projectedModel originalModel : Prop) : Prop :=
  AyMIALConj assumptionModel (AyMIALConj projectedModel originalModel)

def AyMIALProofCompatibility
    (assumptionProof projectedProof originalProof : Prop) : Prop :=
  AyMIALConj assumptionProof (AyMIALConj projectedProof originalProof)

def AyMIALFormulaFingerprint
    (assumptionFingerprint originalFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMIALConj assumptionFingerprint
    (AyMIALConj originalFingerprint fingerprintAgreement)

def AyMIALCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMIALConj checkerAccepted replayTrace

def AyMIALLiftEvidence
    (frameOk activationOk projectionOk modelOk proofOk fingerprintOk replayOk :
      Prop) : Prop :=
  AyMIALConj frameOk
    (AyMIALConj activationOk
      (AyMIALConj projectionOk
        (AyMIALConj modelOk
          (AyMIALConj proofOk
            (AyMIALConj fingerprintOk replayOk)))))

def AyMIALLiftedPublication
    (liftEvidence auditEntry publicResult : Prop) : Prop :=
  AyMIALConj liftEvidence (AyMIALConj auditEntry publicResult)

def AyMIALNoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMIALConj diagnostic (publicClaim -> False)

def AyMIALRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMIALConj reason recomputeRequest

theorem ay_mial_conj_intro {left right : Prop} :
    left -> right -> AyMIALConj left right :=
  fun hleft hright goal k => k hleft hright

theorem ay_mial_conj_left {left right : Prop} :
    AyMIALConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mial_conj_right {left right : Prop} :
    AyMIALConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mial_disj_left {left right : Prop} :
    left -> AyMIALDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mial_disj_right {left right : Prop} :
    right -> AyMIALDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mial_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMIALEquisat left right :=
  fun hf hb => ay_mial_conj_intro hf hb

theorem ay_mial_equisat_forward {left right : Prop} :
    AyMIALEquisat left right -> left -> right :=
  fun h => ay_mial_conj_left h

theorem ay_mial_equisat_backward {left right : Prop} :
    AyMIALEquisat left right -> right -> left :=
  fun h => ay_mial_conj_right h

theorem ay_mial_assumption_frame_lineage_intro
    {rootFrame currentFrame lineageWitness : Prop} :
    rootFrame ->
    currentFrame ->
    lineageWitness ->
    AyMIALAssumptionFrameLineage rootFrame currentFrame lineageWitness :=
  fun hroot hcurrent hlineage =>
    ay_mial_conj_intro hroot
      (ay_mial_conj_intro hcurrent hlineage)

theorem ay_mial_assumption_frame_lineage_root
    {rootFrame currentFrame lineageWitness : Prop} :
    AyMIALAssumptionFrameLineage rootFrame currentFrame lineageWitness ->
    rootFrame :=
  fun h => ay_mial_conj_left h

theorem ay_mial_assumption_frame_lineage_current
    {rootFrame currentFrame lineageWitness : Prop} :
    AyMIALAssumptionFrameLineage rootFrame currentFrame lineageWitness ->
    currentFrame :=
  fun h => ay_mial_conj_left (ay_mial_conj_right h)

theorem ay_mial_assumption_frame_lineage_witness
    {rootFrame currentFrame lineageWitness : Prop} :
    AyMIALAssumptionFrameLineage rootFrame currentFrame lineageWitness ->
    lineageWitness :=
  fun h => ay_mial_conj_right (ay_mial_conj_right h)

theorem ay_mial_activation_mapping_intro
    {activationLiterals activationMap noDroppedActivation : Prop} :
    activationLiterals ->
    activationMap ->
    noDroppedActivation ->
    AyMIALActivationMapping
      activationLiterals activationMap noDroppedActivation :=
  fun hlits hmap hnondrop =>
    ay_mial_conj_intro hlits (ay_mial_conj_intro hmap hnondrop)

theorem ay_mial_activation_mapping_literals
    {activationLiterals activationMap noDroppedActivation : Prop} :
    AyMIALActivationMapping
      activationLiterals activationMap noDroppedActivation ->
    activationLiterals :=
  fun h => ay_mial_conj_left h

theorem ay_mial_activation_mapping_map
    {activationLiterals activationMap noDroppedActivation : Prop} :
    AyMIALActivationMapping
      activationLiterals activationMap noDroppedActivation ->
    activationMap :=
  fun h => ay_mial_conj_left (ay_mial_conj_right h)

theorem ay_mial_activation_mapping_no_dropped
    {activationLiterals activationMap noDroppedActivation : Prop} :
    AyMIALActivationMapping
      activationLiterals activationMap noDroppedActivation ->
    noDroppedActivation :=
  fun h => ay_mial_conj_right (ay_mial_conj_right h)

theorem ay_mial_projection_reconstruction_intro
    {projectionEvidence reconstructionEvidence : Prop} :
    projectionEvidence ->
    reconstructionEvidence ->
    AyMIALProjectionReconstruction
      projectionEvidence reconstructionEvidence :=
  fun hprojection hreconstruction =>
    ay_mial_conj_intro hprojection hreconstruction

theorem ay_mial_projection_reconstruction_projection
    {projectionEvidence reconstructionEvidence : Prop} :
    AyMIALProjectionReconstruction
      projectionEvidence reconstructionEvidence ->
    projectionEvidence :=
  fun h => ay_mial_conj_left h

theorem ay_mial_projection_reconstruction_reconstruction
    {projectionEvidence reconstructionEvidence : Prop} :
    AyMIALProjectionReconstruction
      projectionEvidence reconstructionEvidence ->
    reconstructionEvidence :=
  fun h => ay_mial_conj_right h

theorem ay_mial_model_compatibility_intro
    {assumptionModel projectedModel originalModel : Prop} :
    assumptionModel ->
    projectedModel ->
    originalModel ->
    AyMIALModelCompatibility assumptionModel projectedModel originalModel :=
  fun hassumption hprojected horiginal =>
    ay_mial_conj_intro hassumption
      (ay_mial_conj_intro hprojected horiginal)

theorem ay_mial_model_compatibility_assumption
    {assumptionModel projectedModel originalModel : Prop} :
    AyMIALModelCompatibility assumptionModel projectedModel originalModel ->
    assumptionModel :=
  fun h => ay_mial_conj_left h

theorem ay_mial_model_compatibility_projected
    {assumptionModel projectedModel originalModel : Prop} :
    AyMIALModelCompatibility assumptionModel projectedModel originalModel ->
    projectedModel :=
  fun h => ay_mial_conj_left (ay_mial_conj_right h)

theorem ay_mial_model_compatibility_original
    {assumptionModel projectedModel originalModel : Prop} :
    AyMIALModelCompatibility assumptionModel projectedModel originalModel ->
    originalModel :=
  fun h => ay_mial_conj_right (ay_mial_conj_right h)

theorem ay_mial_proof_compatibility_intro
    {assumptionProof projectedProof originalProof : Prop} :
    assumptionProof ->
    projectedProof ->
    originalProof ->
    AyMIALProofCompatibility assumptionProof projectedProof originalProof :=
  fun hassumption hprojected horiginal =>
    ay_mial_conj_intro hassumption
      (ay_mial_conj_intro hprojected horiginal)

theorem ay_mial_proof_compatibility_assumption
    {assumptionProof projectedProof originalProof : Prop} :
    AyMIALProofCompatibility assumptionProof projectedProof originalProof ->
    assumptionProof :=
  fun h => ay_mial_conj_left h

theorem ay_mial_proof_compatibility_projected
    {assumptionProof projectedProof originalProof : Prop} :
    AyMIALProofCompatibility assumptionProof projectedProof originalProof ->
    projectedProof :=
  fun h => ay_mial_conj_left (ay_mial_conj_right h)

theorem ay_mial_proof_compatibility_original
    {assumptionProof projectedProof originalProof : Prop} :
    AyMIALProofCompatibility assumptionProof projectedProof originalProof ->
    originalProof :=
  fun h => ay_mial_conj_right (ay_mial_conj_right h)

theorem ay_mial_formula_fingerprint_intro
    {assumptionFingerprint originalFingerprint fingerprintAgreement : Prop} :
    assumptionFingerprint ->
    originalFingerprint ->
    fingerprintAgreement ->
    AyMIALFormulaFingerprint
      assumptionFingerprint originalFingerprint fingerprintAgreement :=
  fun hassumption horiginal hagree =>
    ay_mial_conj_intro hassumption
      (ay_mial_conj_intro horiginal hagree)

theorem ay_mial_formula_fingerprint_assumption
    {assumptionFingerprint originalFingerprint fingerprintAgreement : Prop} :
    AyMIALFormulaFingerprint
      assumptionFingerprint originalFingerprint fingerprintAgreement ->
    assumptionFingerprint :=
  fun h => ay_mial_conj_left h

theorem ay_mial_formula_fingerprint_original
    {assumptionFingerprint originalFingerprint fingerprintAgreement : Prop} :
    AyMIALFormulaFingerprint
      assumptionFingerprint originalFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mial_conj_left (ay_mial_conj_right h)

theorem ay_mial_formula_fingerprint_agreement
    {assumptionFingerprint originalFingerprint fingerprintAgreement : Prop} :
    AyMIALFormulaFingerprint
      assumptionFingerprint originalFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mial_conj_right (ay_mial_conj_right h)

theorem ay_mial_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMIALCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mial_conj_intro haccepted htrace

theorem ay_mial_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMIALCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_mial_conj_left h

theorem ay_mial_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMIALCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_mial_conj_right h

theorem ay_mial_lift_evidence_intro
    {frameOk activationOk projectionOk modelOk proofOk fingerprintOk replayOk :
      Prop} :
    frameOk ->
    activationOk ->
    projectionOk ->
    modelOk ->
    proofOk ->
    fingerprintOk ->
    replayOk ->
    AyMIALLiftEvidence
      frameOk activationOk projectionOk modelOk proofOk fingerprintOk
      replayOk :=
  fun hframe hactivation hprojection hmodel hproof hfingerprint hreplay =>
    ay_mial_conj_intro hframe
      (ay_mial_conj_intro hactivation
        (ay_mial_conj_intro hprojection
          (ay_mial_conj_intro hmodel
            (ay_mial_conj_intro hproof
              (ay_mial_conj_intro hfingerprint hreplay)))))

theorem ay_mial_lift_evidence_frame
    {frameOk activationOk projectionOk modelOk proofOk fingerprintOk replayOk :
      Prop} :
    AyMIALLiftEvidence
      frameOk activationOk projectionOk modelOk proofOk fingerprintOk
      replayOk ->
    frameOk :=
  fun h => ay_mial_conj_left h

theorem ay_mial_lift_evidence_activation
    {frameOk activationOk projectionOk modelOk proofOk fingerprintOk replayOk :
      Prop} :
    AyMIALLiftEvidence
      frameOk activationOk projectionOk modelOk proofOk fingerprintOk
      replayOk ->
    activationOk :=
  fun h => ay_mial_conj_left (ay_mial_conj_right h)

theorem ay_mial_lift_evidence_projection
    {frameOk activationOk projectionOk modelOk proofOk fingerprintOk replayOk :
      Prop} :
    AyMIALLiftEvidence
      frameOk activationOk projectionOk modelOk proofOk fingerprintOk
      replayOk ->
    projectionOk :=
  fun h => ay_mial_conj_left (ay_mial_conj_right (ay_mial_conj_right h))

theorem ay_mial_lift_evidence_model
    {frameOk activationOk projectionOk modelOk proofOk fingerprintOk replayOk :
      Prop} :
    AyMIALLiftEvidence
      frameOk activationOk projectionOk modelOk proofOk fingerprintOk
      replayOk ->
    modelOk :=
  fun h =>
    ay_mial_conj_left
      (ay_mial_conj_right (ay_mial_conj_right (ay_mial_conj_right h)))

theorem ay_mial_lift_evidence_proof
    {frameOk activationOk projectionOk modelOk proofOk fingerprintOk replayOk :
      Prop} :
    AyMIALLiftEvidence
      frameOk activationOk projectionOk modelOk proofOk fingerprintOk
      replayOk ->
    proofOk :=
  fun h =>
    ay_mial_conj_left
      (ay_mial_conj_right
        (ay_mial_conj_right (ay_mial_conj_right (ay_mial_conj_right h))))

theorem ay_mial_lift_evidence_fingerprint
    {frameOk activationOk projectionOk modelOk proofOk fingerprintOk replayOk :
      Prop} :
    AyMIALLiftEvidence
      frameOk activationOk projectionOk modelOk proofOk fingerprintOk
      replayOk ->
    fingerprintOk :=
  fun h =>
    ay_mial_conj_left
      (ay_mial_conj_right
        (ay_mial_conj_right
          (ay_mial_conj_right (ay_mial_conj_right (ay_mial_conj_right h)))))

theorem ay_mial_lift_evidence_replay
    {frameOk activationOk projectionOk modelOk proofOk fingerprintOk replayOk :
      Prop} :
    AyMIALLiftEvidence
      frameOk activationOk projectionOk modelOk proofOk fingerprintOk
      replayOk ->
    replayOk :=
  fun h =>
    ay_mial_conj_right
      (ay_mial_conj_right
        (ay_mial_conj_right
          (ay_mial_conj_right (ay_mial_conj_right (ay_mial_conj_right h)))))

theorem ay_mial_lifted_publication_intro
    {liftEvidence auditEntry publicResult : Prop} :
    liftEvidence ->
    auditEntry ->
    publicResult ->
    AyMIALLiftedPublication liftEvidence auditEntry publicResult :=
  fun hevidence haudit hresult =>
    ay_mial_conj_intro hevidence (ay_mial_conj_intro haudit hresult)

theorem ay_mial_lifted_publication_evidence
    {liftEvidence auditEntry publicResult : Prop} :
    AyMIALLiftedPublication liftEvidence auditEntry publicResult ->
    liftEvidence :=
  fun h => ay_mial_conj_left h

theorem ay_mial_lifted_publication_audit
    {liftEvidence auditEntry publicResult : Prop} :
    AyMIALLiftedPublication liftEvidence auditEntry publicResult ->
    auditEntry :=
  fun h => ay_mial_conj_left (ay_mial_conj_right h)

theorem ay_mial_lifted_publication_result
    {liftEvidence auditEntry publicResult : Prop} :
    AyMIALLiftedPublication liftEvidence auditEntry publicResult ->
    publicResult :=
  fun h => ay_mial_conj_right (ay_mial_conj_right h)

theorem ay_mial_accepted_lift_preserves_sat_publication
    {liftEvidence auditEntry publicSatClaim : Prop} :
    AyMIALLiftedPublication liftEvidence auditEntry publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mial_lifted_publication_result h

theorem ay_mial_accepted_lift_preserves_unsat_publication
    {liftEvidence auditEntry publicUnsatClaim : Prop} :
    AyMIALLiftedPublication liftEvidence auditEntry publicUnsatClaim ->
    publicUnsatClaim :=
  fun h => ay_mial_lifted_publication_result h

theorem ay_mial_lifted_publication_sound_exact
    {liftEvidence auditEntry publicResult : Prop} :
    AyMIALEquisat
      (AyMIALLiftedPublication liftEvidence auditEntry publicResult)
      (AyMIALConj liftEvidence (AyMIALConj auditEntry publicResult)) :=
  ay_mial_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_mial_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMIALNoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_mial_conj_intro hdiagnostic hblocks

theorem ay_mial_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMIALNoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_mial_conj_left h

theorem ay_mial_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMIALNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_mial_conj_right h

theorem ay_mial_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMIALRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_mial_conj_intro hreason hrequest

theorem ay_mial_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMIALRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_mial_conj_left h

theorem ay_mial_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMIALRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_mial_conj_right h

theorem ay_mial_stale_assumption_frame_recompute
    {staleAssumptionFrame recomputeRequest : Prop} :
    staleAssumptionFrame ->
    recomputeRequest ->
    AyMIALRecomputeObligation staleAssumptionFrame recomputeRequest :=
  fun hstale hrecompute =>
    ay_mial_recompute_obligation_intro hstale hrecompute

theorem ay_mial_stale_assumption_frame_no_claim
    {staleAssumptionFrame publicClaim : Prop} :
    staleAssumptionFrame ->
    (staleAssumptionFrame -> publicClaim -> False) ->
    AyMIALNoClaimDiagnostic staleAssumptionFrame publicClaim :=
  fun hstale hblocks =>
    ay_mial_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_mial_dropped_activation_no_claim
    {droppedActivation publicClaim : Prop} :
    droppedActivation ->
    (droppedActivation -> publicClaim -> False) ->
    AyMIALNoClaimDiagnostic droppedActivation publicClaim :=
  fun hdropped hblocks =>
    ay_mial_no_claim_diagnostic_intro hdropped (hblocks hdropped)

theorem ay_mial_projection_mismatch_no_claim
    {projectionMismatch publicClaim : Prop} :
    projectionMismatch ->
    (projectionMismatch -> publicClaim -> False) ->
    AyMIALNoClaimDiagnostic projectionMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mial_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mial_model_incompatibility_no_claim
    {modelIncompatibility publicClaim : Prop} :
    modelIncompatibility ->
    (modelIncompatibility -> publicClaim -> False) ->
    AyMIALNoClaimDiagnostic modelIncompatibility publicClaim :=
  fun hbad hblocks =>
    ay_mial_no_claim_diagnostic_intro hbad (hblocks hbad)

theorem ay_mial_proof_incompatibility_no_claim
    {proofIncompatibility publicClaim : Prop} :
    proofIncompatibility ->
    (proofIncompatibility -> publicClaim -> False) ->
    AyMIALNoClaimDiagnostic proofIncompatibility publicClaim :=
  fun hbad hblocks =>
    ay_mial_no_claim_diagnostic_intro hbad (hblocks hbad)

theorem ay_mial_replay_rejection_no_claim
    {replayRejection publicClaim : Prop} :
    replayRejection ->
    (replayRejection -> publicClaim -> False) ->
    AyMIALNoClaimDiagnostic replayRejection publicClaim :=
  fun hreject hblocks =>
    ay_mial_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_mial_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMIALNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_mial_no_claim_diagnostic_blocks h hclaim

theorem ay_mial_bad_assumption_lift_no_stale_publication
    {staleAssumptionFrame droppedActivation projectionMismatch
      modelIncompatibility proofIncompatibility replayRejection
      publicClaim : Prop} :
    (staleAssumptionFrame -> publicClaim -> False) ->
    (droppedActivation -> publicClaim -> False) ->
    (projectionMismatch -> publicClaim -> False) ->
    (modelIncompatibility -> publicClaim -> False) ->
    (proofIncompatibility -> publicClaim -> False) ->
    (replayRejection -> publicClaim -> False) ->
    AyMIALConj
      (staleAssumptionFrame ->
        AyMIALNoClaimDiagnostic staleAssumptionFrame publicClaim)
      (AyMIALConj
        (droppedActivation ->
          AyMIALNoClaimDiagnostic droppedActivation publicClaim)
        (AyMIALConj
          (projectionMismatch ->
            AyMIALNoClaimDiagnostic projectionMismatch publicClaim)
          (AyMIALConj
            (modelIncompatibility ->
              AyMIALNoClaimDiagnostic modelIncompatibility publicClaim)
            (AyMIALConj
              (proofIncompatibility ->
                AyMIALNoClaimDiagnostic proofIncompatibility publicClaim)
              (replayRejection ->
                AyMIALNoClaimDiagnostic replayRejection publicClaim))))) :=
  fun hframe hactivation hprojection hmodel hproof hreplay =>
    ay_mial_conj_intro
      (fun h => ay_mial_stale_assumption_frame_no_claim h hframe)
      (ay_mial_conj_intro
        (fun h => ay_mial_dropped_activation_no_claim h hactivation)
        (ay_mial_conj_intro
          (fun h => ay_mial_projection_mismatch_no_claim h hprojection)
          (ay_mial_conj_intro
            (fun h => ay_mial_model_incompatibility_no_claim h hmodel)
            (ay_mial_conj_intro
              (fun h => ay_mial_proof_incompatibility_no_claim h hproof)
              (fun h => ay_mial_replay_rejection_no_claim h hreplay)))))
