-- SAT-COMP/ay incremental-assumption model projection soundness skeleton.
-- The predicates below name the certificate obligations needed before a model
-- found under assumptions/cubes may be published for the base formula.

def AyMIAPConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMIAPDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMIAPEquisat (left right : Prop) : Prop :=
  AyMIAPConj (left -> right) (right -> left)

def AyMIAPAssumptionFrame (frameId cubeMembership assumptionScope : Prop) : Prop :=
  AyMIAPConj frameId (AyMIAPConj cubeMembership assumptionScope)

def AyMIAPProjectionMap (assumptionModel baseVisibleModel : Prop) : Prop :=
  assumptionModel -> baseVisibleModel

def AyMIAPExtensionEvidence (baseVisibleModel baseOriginalModel : Prop) : Prop :=
  baseVisibleModel -> baseOriginalModel

def AyMIAPFormulaFingerprint (assumptionFingerprint baseFingerprint : Prop) : Prop :=
  AyMIAPConj assumptionFingerprint baseFingerprint

def AyMIAPCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMIAPConj checkerAccepted replayTrace

def AyMIAPSoundProjectionEvidence
    (frameOk projectionOk extensionOk fingerprintOk replayOk : Prop) : Prop :=
  AyMIAPConj frameOk
    (AyMIAPConj projectionOk
      (AyMIAPConj extensionOk
        (AyMIAPConj fingerprintOk replayOk)))

def AyMIAPAcceptedSatReport
    (projectionEvidence auditEntry baseOriginalModel : Prop) : Prop :=
  AyMIAPConj projectionEvidence (AyMIAPConj auditEntry baseOriginalModel)

def AyMIAPNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMIAPConj diagnostic (publicSatClaim -> False)

def AyMIAPRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMIAPConj reason recomputeRequest

theorem ay_miap_conj_intro {left right : Prop} :
    left -> right -> AyMIAPConj left right :=
  fun hleft hright goal k => k hleft hright

theorem ay_miap_conj_left {left right : Prop} :
    AyMIAPConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_miap_conj_right {left right : Prop} :
    AyMIAPConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_miap_disj_left {left right : Prop} :
    left -> AyMIAPDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_miap_disj_right {left right : Prop} :
    right -> AyMIAPDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_miap_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMIAPEquisat left right :=
  fun hf hb => ay_miap_conj_intro hf hb

theorem ay_miap_equisat_forward {left right : Prop} :
    AyMIAPEquisat left right -> left -> right :=
  fun h => ay_miap_conj_left h

theorem ay_miap_equisat_backward {left right : Prop} :
    AyMIAPEquisat left right -> right -> left :=
  fun h => ay_miap_conj_right h

theorem ay_miap_assumption_frame_intro
    {frameId cubeMembership assumptionScope : Prop} :
    frameId ->
    cubeMembership ->
    assumptionScope ->
    AyMIAPAssumptionFrame frameId cubeMembership assumptionScope :=
  fun hframe hcube hscope =>
    ay_miap_conj_intro hframe (ay_miap_conj_intro hcube hscope)

theorem ay_miap_assumption_frame_id
    {frameId cubeMembership assumptionScope : Prop} :
    AyMIAPAssumptionFrame frameId cubeMembership assumptionScope ->
    frameId :=
  fun h => ay_miap_conj_left h

theorem ay_miap_assumption_frame_cube
    {frameId cubeMembership assumptionScope : Prop} :
    AyMIAPAssumptionFrame frameId cubeMembership assumptionScope ->
    cubeMembership :=
  fun h => ay_miap_conj_left (ay_miap_conj_right h)

theorem ay_miap_assumption_frame_scope
    {frameId cubeMembership assumptionScope : Prop} :
    AyMIAPAssumptionFrame frameId cubeMembership assumptionScope ->
    assumptionScope :=
  fun h => ay_miap_conj_right (ay_miap_conj_right h)

theorem ay_miap_projection_map_apply
    {assumptionModel baseVisibleModel : Prop} :
    AyMIAPProjectionMap assumptionModel baseVisibleModel ->
    assumptionModel ->
    baseVisibleModel :=
  fun hmap hmodel => hmap hmodel

theorem ay_miap_extension_evidence_apply
    {baseVisibleModel baseOriginalModel : Prop} :
    AyMIAPExtensionEvidence baseVisibleModel baseOriginalModel ->
    baseVisibleModel ->
    baseOriginalModel :=
  fun hext hvisible => hext hvisible

theorem ay_miap_formula_fingerprint_intro
    {assumptionFingerprint baseFingerprint : Prop} :
    assumptionFingerprint ->
    baseFingerprint ->
    AyMIAPFormulaFingerprint assumptionFingerprint baseFingerprint :=
  fun hassumption hbase => ay_miap_conj_intro hassumption hbase

theorem ay_miap_formula_fingerprint_assumption
    {assumptionFingerprint baseFingerprint : Prop} :
    AyMIAPFormulaFingerprint assumptionFingerprint baseFingerprint ->
    assumptionFingerprint :=
  fun h => ay_miap_conj_left h

theorem ay_miap_formula_fingerprint_base
    {assumptionFingerprint baseFingerprint : Prop} :
    AyMIAPFormulaFingerprint assumptionFingerprint baseFingerprint ->
    baseFingerprint :=
  fun h => ay_miap_conj_right h

theorem ay_miap_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMIAPCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_miap_conj_intro haccepted htrace

theorem ay_miap_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMIAPCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_miap_conj_left h

theorem ay_miap_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMIAPCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_miap_conj_right h

theorem ay_miap_sound_projection_evidence_intro
    {frameOk projectionOk extensionOk fingerprintOk replayOk : Prop} :
    frameOk ->
    projectionOk ->
    extensionOk ->
    fingerprintOk ->
    replayOk ->
    AyMIAPSoundProjectionEvidence
      frameOk projectionOk extensionOk fingerprintOk replayOk :=
  fun hframe hprojection hextension hfingerprint hreplay =>
    ay_miap_conj_intro hframe
      (ay_miap_conj_intro hprojection
        (ay_miap_conj_intro hextension
          (ay_miap_conj_intro hfingerprint hreplay)))

theorem ay_miap_sound_projection_evidence_frame
    {frameOk projectionOk extensionOk fingerprintOk replayOk : Prop} :
    AyMIAPSoundProjectionEvidence
      frameOk projectionOk extensionOk fingerprintOk replayOk ->
    frameOk :=
  fun h => ay_miap_conj_left h

theorem ay_miap_sound_projection_evidence_projection
    {frameOk projectionOk extensionOk fingerprintOk replayOk : Prop} :
    AyMIAPSoundProjectionEvidence
      frameOk projectionOk extensionOk fingerprintOk replayOk ->
    projectionOk :=
  fun h => ay_miap_conj_left (ay_miap_conj_right h)

theorem ay_miap_sound_projection_evidence_extension
    {frameOk projectionOk extensionOk fingerprintOk replayOk : Prop} :
    AyMIAPSoundProjectionEvidence
      frameOk projectionOk extensionOk fingerprintOk replayOk ->
    extensionOk :=
  fun h => ay_miap_conj_left (ay_miap_conj_right (ay_miap_conj_right h))

theorem ay_miap_sound_projection_evidence_fingerprint
    {frameOk projectionOk extensionOk fingerprintOk replayOk : Prop} :
    AyMIAPSoundProjectionEvidence
      frameOk projectionOk extensionOk fingerprintOk replayOk ->
    fingerprintOk :=
  fun h =>
    ay_miap_conj_left
      (ay_miap_conj_right (ay_miap_conj_right (ay_miap_conj_right h)))

theorem ay_miap_sound_projection_evidence_replay
    {frameOk projectionOk extensionOk fingerprintOk replayOk : Prop} :
    AyMIAPSoundProjectionEvidence
      frameOk projectionOk extensionOk fingerprintOk replayOk ->
    replayOk :=
  fun h =>
    ay_miap_conj_right
      (ay_miap_conj_right (ay_miap_conj_right (ay_miap_conj_right h)))

theorem ay_miap_report_intro
    {projectionEvidence auditEntry baseOriginalModel : Prop} :
    projectionEvidence ->
    auditEntry ->
    baseOriginalModel ->
    AyMIAPAcceptedSatReport projectionEvidence auditEntry baseOriginalModel :=
  fun hevidence haudit hmodel =>
    ay_miap_conj_intro hevidence (ay_miap_conj_intro haudit hmodel)

theorem ay_miap_report_evidence
    {projectionEvidence auditEntry baseOriginalModel : Prop} :
    AyMIAPAcceptedSatReport projectionEvidence auditEntry baseOriginalModel ->
    projectionEvidence :=
  fun h => ay_miap_conj_left h

theorem ay_miap_report_audit
    {projectionEvidence auditEntry baseOriginalModel : Prop} :
    AyMIAPAcceptedSatReport projectionEvidence auditEntry baseOriginalModel ->
    auditEntry :=
  fun h => ay_miap_conj_left (ay_miap_conj_right h)

theorem ay_miap_report_base_original_model
    {projectionEvidence auditEntry baseOriginalModel : Prop} :
    AyMIAPAcceptedSatReport projectionEvidence auditEntry baseOriginalModel ->
    baseOriginalModel :=
  fun h => ay_miap_conj_right (ay_miap_conj_right h)

theorem ay_miap_assumption_model_projects_to_base
    {assumptionModel baseVisibleModel baseOriginalModel : Prop} :
    AyMIAPProjectionMap assumptionModel baseVisibleModel ->
    AyMIAPExtensionEvidence baseVisibleModel baseOriginalModel ->
    assumptionModel ->
    baseOriginalModel :=
  fun hmap hext hmodel =>
    hext (hmap hmodel)

theorem ay_miap_accepted_report_from_incremental_model
    {assumptionModel baseVisibleModel baseOriginalModel frameOk projectionOk
      extensionOk fingerprintOk replayOk auditEntry : Prop} :
    AyMIAPProjectionMap assumptionModel baseVisibleModel ->
    AyMIAPExtensionEvidence baseVisibleModel baseOriginalModel ->
    assumptionModel ->
    AyMIAPSoundProjectionEvidence
      frameOk projectionOk extensionOk fingerprintOk replayOk ->
    auditEntry ->
    AyMIAPAcceptedSatReport
      (AyMIAPSoundProjectionEvidence
        frameOk projectionOk extensionOk fingerprintOk replayOk)
      auditEntry
      baseOriginalModel :=
  fun hmap hext hmodel hevidence haudit =>
    ay_miap_report_intro hevidence haudit
      (ay_miap_assumption_model_projects_to_base hmap hext hmodel)

theorem ay_miap_report_requires_assumption_frame
    {frameOk projectionOk extensionOk fingerprintOk replayOk auditEntry
      baseOriginalModel : Prop} :
    AyMIAPAcceptedSatReport
      (AyMIAPSoundProjectionEvidence
        frameOk projectionOk extensionOk fingerprintOk replayOk)
      auditEntry
      baseOriginalModel ->
    frameOk :=
  fun h =>
    ay_miap_sound_projection_evidence_frame (ay_miap_report_evidence h)

theorem ay_miap_report_requires_projection_map
    {frameOk projectionOk extensionOk fingerprintOk replayOk auditEntry
      baseOriginalModel : Prop} :
    AyMIAPAcceptedSatReport
      (AyMIAPSoundProjectionEvidence
        frameOk projectionOk extensionOk fingerprintOk replayOk)
      auditEntry
      baseOriginalModel ->
    projectionOk :=
  fun h =>
    ay_miap_sound_projection_evidence_projection (ay_miap_report_evidence h)

theorem ay_miap_report_requires_extension_evidence
    {frameOk projectionOk extensionOk fingerprintOk replayOk auditEntry
      baseOriginalModel : Prop} :
    AyMIAPAcceptedSatReport
      (AyMIAPSoundProjectionEvidence
        frameOk projectionOk extensionOk fingerprintOk replayOk)
      auditEntry
      baseOriginalModel ->
    extensionOk :=
  fun h =>
    ay_miap_sound_projection_evidence_extension (ay_miap_report_evidence h)

theorem ay_miap_report_requires_fingerprint
    {frameOk projectionOk extensionOk fingerprintOk replayOk auditEntry
      baseOriginalModel : Prop} :
    AyMIAPAcceptedSatReport
      (AyMIAPSoundProjectionEvidence
        frameOk projectionOk extensionOk fingerprintOk replayOk)
      auditEntry
      baseOriginalModel ->
    fingerprintOk :=
  fun h =>
    ay_miap_sound_projection_evidence_fingerprint (ay_miap_report_evidence h)

theorem ay_miap_report_requires_checker_replay
    {frameOk projectionOk extensionOk fingerprintOk replayOk auditEntry
      baseOriginalModel : Prop} :
    AyMIAPAcceptedSatReport
      (AyMIAPSoundProjectionEvidence
        frameOk projectionOk extensionOk fingerprintOk replayOk)
      auditEntry
      baseOriginalModel ->
    replayOk :=
  fun h =>
    ay_miap_sound_projection_evidence_replay (ay_miap_report_evidence h)

theorem ay_miap_report_sound_exact
    {projectionEvidence auditEntry baseOriginalModel : Prop} :
    AyMIAPEquisat
      (AyMIAPAcceptedSatReport projectionEvidence auditEntry baseOriginalModel)
      (AyMIAPConj projectionEvidence (AyMIAPConj auditEntry baseOriginalModel)) :=
  ay_miap_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_miap_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMIAPNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks => ay_miap_conj_intro hdiagnostic hblocks

theorem ay_miap_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMIAPNoClaimDiagnostic diagnostic publicSatClaim ->
    diagnostic :=
  fun h => ay_miap_conj_left h

theorem ay_miap_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMIAPNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_miap_conj_right h

theorem ay_miap_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMIAPRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_miap_conj_intro hreason hrequest

theorem ay_miap_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMIAPRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_miap_conj_left h

theorem ay_miap_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMIAPRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_miap_conj_right h

theorem ay_miap_frame_mismatch_recompute
    {frameMismatch recomputeRequest : Prop} :
    frameMismatch ->
    recomputeRequest ->
    AyMIAPRecomputeObligation frameMismatch recomputeRequest :=
  fun hmismatch hrecompute =>
    ay_miap_recompute_obligation_intro hmismatch hrecompute

theorem ay_miap_frame_mismatch_no_claim
    {frameMismatch publicSatClaim : Prop} :
    frameMismatch ->
    (frameMismatch -> publicSatClaim -> False) ->
    AyMIAPNoClaimDiagnostic frameMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_miap_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_miap_projection_mismatch_no_claim
    {projectionMismatch publicSatClaim : Prop} :
    projectionMismatch ->
    (projectionMismatch -> publicSatClaim -> False) ->
    AyMIAPNoClaimDiagnostic projectionMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_miap_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_miap_extension_missing_no_claim
    {extensionMissing publicSatClaim : Prop} :
    extensionMissing ->
    (extensionMissing -> publicSatClaim -> False) ->
    AyMIAPNoClaimDiagnostic extensionMissing publicSatClaim :=
  fun hmissing hblocks =>
    ay_miap_no_claim_diagnostic_intro hmissing (hblocks hmissing)

theorem ay_miap_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicSatClaim : Prop} :
    fingerprintMismatch ->
    (fingerprintMismatch -> publicSatClaim -> False) ->
    AyMIAPNoClaimDiagnostic fingerprintMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_miap_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_miap_checker_replay_reject_no_claim
    {checkerReplayReject publicSatClaim : Prop} :
    checkerReplayReject ->
    (checkerReplayReject -> publicSatClaim -> False) ->
    AyMIAPNoClaimDiagnostic checkerReplayReject publicSatClaim :=
  fun hreject hblocks =>
    ay_miap_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_miap_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMIAPNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_miap_no_claim_diagnostic_blocks h hclaim

theorem ay_miap_bad_incremental_assumption_no_stale_sat
    {frameMismatch projectionMismatch extensionMissing fingerprintMismatch
      checkerReplayReject publicSatClaim : Prop} :
    (frameMismatch -> publicSatClaim -> False) ->
    (projectionMismatch -> publicSatClaim -> False) ->
    (extensionMissing -> publicSatClaim -> False) ->
    (fingerprintMismatch -> publicSatClaim -> False) ->
    (checkerReplayReject -> publicSatClaim -> False) ->
    AyMIAPConj
      (frameMismatch ->
        AyMIAPNoClaimDiagnostic frameMismatch publicSatClaim)
      (AyMIAPConj
        (projectionMismatch ->
          AyMIAPNoClaimDiagnostic projectionMismatch publicSatClaim)
        (AyMIAPConj
          (extensionMissing ->
            AyMIAPNoClaimDiagnostic extensionMissing publicSatClaim)
          (AyMIAPConj
            (fingerprintMismatch ->
              AyMIAPNoClaimDiagnostic fingerprintMismatch publicSatClaim)
            (checkerReplayReject ->
              AyMIAPNoClaimDiagnostic checkerReplayReject publicSatClaim)))) :=
  fun hframe hprojection hextension hfingerprint hreplay =>
    ay_miap_conj_intro
      (fun h => ay_miap_frame_mismatch_no_claim h hframe)
      (ay_miap_conj_intro
        (fun h => ay_miap_projection_mismatch_no_claim h hprojection)
        (ay_miap_conj_intro
          (fun h => ay_miap_extension_missing_no_claim h hextension)
          (ay_miap_conj_intro
            (fun h => ay_miap_fingerprint_mismatch_no_claim h hfingerprint)
            (fun h => ay_miap_checker_replay_reject_no_claim h hreplay))))
