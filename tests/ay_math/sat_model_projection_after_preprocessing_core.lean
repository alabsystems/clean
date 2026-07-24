-- SAT-COMP/ay model projection after preprocessing soundness skeleton.
-- This file is intentionally self-contained and propositional: the predicates
-- name the proof obligations that the ay certificate pipeline must discharge.

def AyMPAPConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMPAPDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMPAPEquisat (left right : Prop) : Prop :=
  AyMPAPConj (left -> right) (right -> left)

def AyMPAPProjectionMap (preprocessedModel visibleModel : Prop) : Prop :=
  preprocessedModel -> visibleModel

def AyMPAPOriginalExtension (visibleModel originalModel : Prop) : Prop :=
  visibleModel -> originalModel

def AyMPAPEliminatedVariables (eliminatedDomain reconstructionWitness : Prop) : Prop :=
  AyMPAPConj eliminatedDomain reconstructionWitness

def AyMPAPStageCertificates (stageCertificate certificateChain : Prop) : Prop :=
  AyMPAPConj stageCertificate certificateChain

def AyMPAPFormulaFingerprint (preprocessedFingerprint originalFingerprint : Prop) : Prop :=
  AyMPAPConj preprocessedFingerprint originalFingerprint

def AyMPAPProjectionEvidence
    (projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk : Prop) : Prop :=
  AyMPAPConj projectionMapOk
    (AyMPAPConj eliminatedOk
      (AyMPAPConj stagesOk
        (AyMPAPConj fingerprintOk checkerOk)))

def AyMPAPAcceptedSatReport
    (projectionEvidence auditEntry originalModel : Prop) : Prop :=
  AyMPAPConj projectionEvidence (AyMPAPConj auditEntry originalModel)

def AyMPAPNoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMPAPConj diagnostic (publicSatClaim -> False)

def AyMPAPRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMPAPConj reason recomputeRequest

theorem ay_mpap_conj_intro {left right : Prop} :
    left -> right -> AyMPAPConj left right :=
  fun hleft hright goal k => k hleft hright

theorem ay_mpap_conj_left {left right : Prop} :
    AyMPAPConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mpap_conj_right {left right : Prop} :
    AyMPAPConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mpap_disj_left {left right : Prop} :
    left -> AyMPAPDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mpap_disj_right {left right : Prop} :
    right -> AyMPAPDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mpap_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMPAPEquisat left right :=
  fun hf hb => ay_mpap_conj_intro hf hb

theorem ay_mpap_equisat_forward {left right : Prop} :
    AyMPAPEquisat left right -> left -> right :=
  fun h => ay_mpap_conj_left h

theorem ay_mpap_equisat_backward {left right : Prop} :
    AyMPAPEquisat left right -> right -> left :=
  fun h => ay_mpap_conj_right h

theorem ay_mpap_projection_map_apply
    {preprocessedModel visibleModel : Prop} :
    AyMPAPProjectionMap preprocessedModel visibleModel ->
    preprocessedModel ->
    visibleModel :=
  fun hmap hmodel => hmap hmodel

theorem ay_mpap_original_extension_apply
    {visibleModel originalModel : Prop} :
    AyMPAPOriginalExtension visibleModel originalModel ->
    visibleModel ->
    originalModel :=
  fun hext hvisible => hext hvisible

theorem ay_mpap_eliminated_variables_intro
    {eliminatedDomain reconstructionWitness : Prop} :
    eliminatedDomain ->
    reconstructionWitness ->
    AyMPAPEliminatedVariables eliminatedDomain reconstructionWitness :=
  fun hdomain hwitness => ay_mpap_conj_intro hdomain hwitness

theorem ay_mpap_eliminated_variables_domain
    {eliminatedDomain reconstructionWitness : Prop} :
    AyMPAPEliminatedVariables eliminatedDomain reconstructionWitness ->
    eliminatedDomain :=
  fun h => ay_mpap_conj_left h

theorem ay_mpap_eliminated_variables_witness
    {eliminatedDomain reconstructionWitness : Prop} :
    AyMPAPEliminatedVariables eliminatedDomain reconstructionWitness ->
    reconstructionWitness :=
  fun h => ay_mpap_conj_right h

theorem ay_mpap_stage_certificates_intro
    {stageCertificate certificateChain : Prop} :
    stageCertificate ->
    certificateChain ->
    AyMPAPStageCertificates stageCertificate certificateChain :=
  fun hstage hchain => ay_mpap_conj_intro hstage hchain

theorem ay_mpap_stage_certificates_stage
    {stageCertificate certificateChain : Prop} :
    AyMPAPStageCertificates stageCertificate certificateChain ->
    stageCertificate :=
  fun h => ay_mpap_conj_left h

theorem ay_mpap_stage_certificates_chain
    {stageCertificate certificateChain : Prop} :
    AyMPAPStageCertificates stageCertificate certificateChain ->
    certificateChain :=
  fun h => ay_mpap_conj_right h

theorem ay_mpap_formula_fingerprint_intro
    {preprocessedFingerprint originalFingerprint : Prop} :
    preprocessedFingerprint ->
    originalFingerprint ->
    AyMPAPFormulaFingerprint preprocessedFingerprint originalFingerprint :=
  fun hpre horig => ay_mpap_conj_intro hpre horig

theorem ay_mpap_formula_fingerprint_preprocessed
    {preprocessedFingerprint originalFingerprint : Prop} :
    AyMPAPFormulaFingerprint preprocessedFingerprint originalFingerprint ->
    preprocessedFingerprint :=
  fun h => ay_mpap_conj_left h

theorem ay_mpap_formula_fingerprint_original
    {preprocessedFingerprint originalFingerprint : Prop} :
    AyMPAPFormulaFingerprint preprocessedFingerprint originalFingerprint ->
    originalFingerprint :=
  fun h => ay_mpap_conj_right h

theorem ay_mpap_projection_evidence_intro
    {projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk : Prop} :
    projectionMapOk ->
    eliminatedOk ->
    stagesOk ->
    fingerprintOk ->
    checkerOk ->
    AyMPAPProjectionEvidence
      projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk :=
  fun hmap helim hstages hfingerprint hchecker =>
    ay_mpap_conj_intro hmap
      (ay_mpap_conj_intro helim
        (ay_mpap_conj_intro hstages
          (ay_mpap_conj_intro hfingerprint hchecker)))

theorem ay_mpap_projection_evidence_projection
    {projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk : Prop} :
    AyMPAPProjectionEvidence
      projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk ->
    projectionMapOk :=
  fun h => ay_mpap_conj_left h

theorem ay_mpap_projection_evidence_eliminated
    {projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk : Prop} :
    AyMPAPProjectionEvidence
      projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk ->
    eliminatedOk :=
  fun h => ay_mpap_conj_left (ay_mpap_conj_right h)

theorem ay_mpap_projection_evidence_stages
    {projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk : Prop} :
    AyMPAPProjectionEvidence
      projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk ->
    stagesOk :=
  fun h => ay_mpap_conj_left (ay_mpap_conj_right (ay_mpap_conj_right h))

theorem ay_mpap_projection_evidence_fingerprint
    {projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk : Prop} :
    AyMPAPProjectionEvidence
      projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk ->
    fingerprintOk :=
  fun h =>
    ay_mpap_conj_left
      (ay_mpap_conj_right (ay_mpap_conj_right (ay_mpap_conj_right h)))

theorem ay_mpap_projection_evidence_checker
    {projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk : Prop} :
    AyMPAPProjectionEvidence
      projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk ->
    checkerOk :=
  fun h =>
    ay_mpap_conj_right
      (ay_mpap_conj_right (ay_mpap_conj_right (ay_mpap_conj_right h)))

theorem ay_mpap_report_intro
    {projectionEvidence auditEntry originalModel : Prop} :
    projectionEvidence ->
    auditEntry ->
    originalModel ->
    AyMPAPAcceptedSatReport projectionEvidence auditEntry originalModel :=
  fun hevidence haudit horiginal =>
    ay_mpap_conj_intro hevidence (ay_mpap_conj_intro haudit horiginal)

theorem ay_mpap_report_evidence
    {projectionEvidence auditEntry originalModel : Prop} :
    AyMPAPAcceptedSatReport projectionEvidence auditEntry originalModel ->
    projectionEvidence :=
  fun h => ay_mpap_conj_left h

theorem ay_mpap_report_audit
    {projectionEvidence auditEntry originalModel : Prop} :
    AyMPAPAcceptedSatReport projectionEvidence auditEntry originalModel ->
    auditEntry :=
  fun h => ay_mpap_conj_left (ay_mpap_conj_right h)

theorem ay_mpap_report_original
    {projectionEvidence auditEntry originalModel : Prop} :
    AyMPAPAcceptedSatReport projectionEvidence auditEntry originalModel ->
    originalModel :=
  fun h => ay_mpap_conj_right (ay_mpap_conj_right h)

theorem ay_mpap_projected_original_model
    {preprocessedModel visibleModel originalModel : Prop} :
    AyMPAPProjectionMap preprocessedModel visibleModel ->
    AyMPAPOriginalExtension visibleModel originalModel ->
    preprocessedModel ->
    originalModel :=
  fun hmap hext hpre =>
    hext (hmap hpre)

theorem ay_mpap_projected_report_from_evidence
    {preprocessedModel visibleModel originalModel projectionMapOk eliminatedOk
      stagesOk fingerprintOk checkerOk auditEntry : Prop} :
    AyMPAPProjectionMap preprocessedModel visibleModel ->
    AyMPAPOriginalExtension visibleModel originalModel ->
    preprocessedModel ->
    AyMPAPProjectionEvidence
      projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk ->
    auditEntry ->
    AyMPAPAcceptedSatReport
      (AyMPAPProjectionEvidence
        projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk)
      auditEntry
      originalModel :=
  fun hmap hext hpre hevidence haudit =>
    ay_mpap_report_intro hevidence haudit
      (ay_mpap_projected_original_model hmap hext hpre)

theorem ay_mpap_report_requires_projection_map
    {projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk auditEntry
      originalModel : Prop} :
    AyMPAPAcceptedSatReport
      (AyMPAPProjectionEvidence
        projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk)
      auditEntry
      originalModel ->
    projectionMapOk :=
  fun h =>
    ay_mpap_projection_evidence_projection (ay_mpap_report_evidence h)

theorem ay_mpap_report_requires_eliminated_variables
    {projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk auditEntry
      originalModel : Prop} :
    AyMPAPAcceptedSatReport
      (AyMPAPProjectionEvidence
        projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk)
      auditEntry
      originalModel ->
    eliminatedOk :=
  fun h =>
    ay_mpap_projection_evidence_eliminated (ay_mpap_report_evidence h)

theorem ay_mpap_report_requires_stage_certificates
    {projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk auditEntry
      originalModel : Prop} :
    AyMPAPAcceptedSatReport
      (AyMPAPProjectionEvidence
        projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk)
      auditEntry
      originalModel ->
    stagesOk :=
  fun h =>
    ay_mpap_projection_evidence_stages (ay_mpap_report_evidence h)

theorem ay_mpap_report_requires_fingerprint
    {projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk auditEntry
      originalModel : Prop} :
    AyMPAPAcceptedSatReport
      (AyMPAPProjectionEvidence
        projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk)
      auditEntry
      originalModel ->
    fingerprintOk :=
  fun h =>
    ay_mpap_projection_evidence_fingerprint (ay_mpap_report_evidence h)

theorem ay_mpap_report_requires_checker
    {projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk auditEntry
      originalModel : Prop} :
    AyMPAPAcceptedSatReport
      (AyMPAPProjectionEvidence
        projectionMapOk eliminatedOk stagesOk fingerprintOk checkerOk)
      auditEntry
      originalModel ->
    checkerOk :=
  fun h =>
    ay_mpap_projection_evidence_checker (ay_mpap_report_evidence h)

theorem ay_mpap_report_sound_exact
    {projectionEvidence auditEntry originalModel : Prop} :
    AyMPAPEquisat
      (AyMPAPAcceptedSatReport projectionEvidence auditEntry originalModel)
      (AyMPAPConj projectionEvidence (AyMPAPConj auditEntry originalModel)) :=
  ay_mpap_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_mpap_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMPAPNoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks => ay_mpap_conj_intro hdiagnostic hblocks

theorem ay_mpap_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMPAPNoClaimDiagnostic diagnostic publicSatClaim ->
    diagnostic :=
  fun h => ay_mpap_conj_left h

theorem ay_mpap_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMPAPNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_mpap_conj_right h

theorem ay_mpap_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMPAPRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_mpap_conj_intro hreason hrequest

theorem ay_mpap_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMPAPRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_mpap_conj_left h

theorem ay_mpap_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMPAPRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_mpap_conj_right h

theorem ay_mpap_missing_projection_entry_recompute
    {missingProjectionEntry recomputeRequest : Prop} :
    missingProjectionEntry ->
    recomputeRequest ->
    AyMPAPRecomputeObligation missingProjectionEntry recomputeRequest :=
  fun hmissing hrecompute =>
    ay_mpap_recompute_obligation_intro hmissing hrecompute

theorem ay_mpap_missing_projection_entry_no_claim
    {missingProjectionEntry publicSatClaim : Prop} :
    missingProjectionEntry ->
    (missingProjectionEntry -> publicSatClaim -> False) ->
    AyMPAPNoClaimDiagnostic missingProjectionEntry publicSatClaim :=
  fun hmissing hblocks =>
    ay_mpap_no_claim_diagnostic_intro hmissing (hblocks hmissing)

theorem ay_mpap_stale_preprocessing_map_no_claim
    {stalePreprocessingMap publicSatClaim : Prop} :
    stalePreprocessingMap ->
    (stalePreprocessingMap -> publicSatClaim -> False) ->
    AyMPAPNoClaimDiagnostic stalePreprocessingMap publicSatClaim :=
  fun hstale hblocks =>
    ay_mpap_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_mpap_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicSatClaim : Prop} :
    fingerprintMismatch ->
    (fingerprintMismatch -> publicSatClaim -> False) ->
    AyMPAPNoClaimDiagnostic fingerprintMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mpap_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mpap_checker_reject_no_claim
    {checkerReject publicSatClaim : Prop} :
    checkerReject ->
    (checkerReject -> publicSatClaim -> False) ->
    AyMPAPNoClaimDiagnostic checkerReject publicSatClaim :=
  fun hreject hblocks =>
    ay_mpap_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_mpap_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMPAPNoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mpap_no_claim_diagnostic_blocks h hclaim

theorem ay_mpap_bad_projection_no_stale_sat
    {missingProjectionEntry stalePreprocessingMap fingerprintMismatch
      checkerReject publicSatClaim : Prop} :
    (missingProjectionEntry -> publicSatClaim -> False) ->
    (stalePreprocessingMap -> publicSatClaim -> False) ->
    (fingerprintMismatch -> publicSatClaim -> False) ->
    (checkerReject -> publicSatClaim -> False) ->
    AyMPAPConj
      (missingProjectionEntry ->
        AyMPAPNoClaimDiagnostic missingProjectionEntry publicSatClaim)
      (AyMPAPConj
        (stalePreprocessingMap ->
          AyMPAPNoClaimDiagnostic stalePreprocessingMap publicSatClaim)
        (AyMPAPConj
          (fingerprintMismatch ->
            AyMPAPNoClaimDiagnostic fingerprintMismatch publicSatClaim)
          (checkerReject ->
            AyMPAPNoClaimDiagnostic checkerReject publicSatClaim))) :=
  fun hmissing hstale hfingerprint hchecker =>
    ay_mpap_conj_intro
      (fun h =>
        ay_mpap_missing_projection_entry_no_claim h hmissing)
      (ay_mpap_conj_intro
        (fun h =>
          ay_mpap_stale_preprocessing_map_no_claim h hstale)
        (ay_mpap_conj_intro
          (fun h =>
            ay_mpap_fingerprint_mismatch_no_claim h hfingerprint)
          (fun h =>
            ay_mpap_checker_reject_no_claim h hchecker)))
