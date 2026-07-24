-- SAT-COMP/ay public SAT model witness minimization soundness skeleton.
-- ay may omit redundant assignment literals only when minimization,
-- re-extension, frame/fingerprint agreement, replay, and manifest digest
-- evidence all agree.

def AyMCWMConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMCWMDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMCWMEquisat (left right : Prop) : Prop :=
  AyMCWMConj (left -> right) (right -> left)

def AyMCWMMinimizationEvidence
    (originalWitness minimizedWitness omittedRedundant : Prop) : Prop :=
  AyMCWMConj originalWitness
    (AyMCWMConj minimizedWitness omittedRedundant)

def AyMCWMExtensionDefaults
    (defaultAssignments extensionMap defaultsComplete : Prop) : Prop :=
  AyMCWMConj defaultAssignments
    (AyMCWMConj extensionMap defaultsComplete)

def AyMCWMFrameCompatibility
    (cubeFrame assumptionFrame refinementFrame : Prop) : Prop :=
  AyMCWMConj cubeFrame (AyMCWMConj assumptionFrame refinementFrame)

def AyMCWMFormulaFingerprint
    (minimizedFingerprint originalFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMCWMConj minimizedFingerprint
    (AyMCWMConj originalFingerprint fingerprintAgreement)

def AyMCWMModelCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMCWMConj checkerAccepted replayTrace

def AyMCWMManifestDigest
    (manifestEntry witnessDigest digestAgreement : Prop) : Prop :=
  AyMCWMConj manifestEntry (AyMCWMConj witnessDigest digestAgreement)

def AyMCWMReExtension
    (minimizedAssignment publicAssignment : Prop) : Prop :=
  minimizedAssignment -> publicAssignment

def AyMCWMPublicationEvidence
    (minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk :
      Prop) : Prop :=
  AyMCWMConj minimizationOk
    (AyMCWMConj defaultsOk
      (AyMCWMConj frameOk
        (AyMCWMConj fingerprintOk
          (AyMCWMConj checkerOk digestOk))))

def AyMCWMMinimizedSatPublication
    (publicationEvidence auditEntry publicSatModel : Prop) : Prop :=
  AyMCWMConj publicationEvidence
    (AyMCWMConj auditEntry publicSatModel)

def AyMCWMNoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMCWMConj diagnostic (publicClaim -> False)

def AyMCWMRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMCWMConj reason recomputeRequest

theorem ay_mcwm_conj_intro {left right : Prop} :
    left -> right -> AyMCWMConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mcwm_conj_left {left right : Prop} :
    AyMCWMConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mcwm_conj_right {left right : Prop} :
    AyMCWMConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mcwm_disj_left {left right : Prop} :
    left -> AyMCWMDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mcwm_disj_right {left right : Prop} :
    right -> AyMCWMDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mcwm_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMCWMEquisat left right :=
  fun hf hb => ay_mcwm_conj_intro hf hb

theorem ay_mcwm_equisat_forward {left right : Prop} :
    AyMCWMEquisat left right -> left -> right :=
  fun h => ay_mcwm_conj_left h

theorem ay_mcwm_equisat_backward {left right : Prop} :
    AyMCWMEquisat left right -> right -> left :=
  fun h => ay_mcwm_conj_right h

theorem ay_mcwm_minimization_evidence_intro
    {originalWitness minimizedWitness omittedRedundant : Prop} :
    originalWitness ->
    minimizedWitness ->
    omittedRedundant ->
    AyMCWMMinimizationEvidence
      originalWitness minimizedWitness omittedRedundant :=
  fun horiginal hminimized homitted =>
    ay_mcwm_conj_intro horiginal
      (ay_mcwm_conj_intro hminimized homitted)

theorem ay_mcwm_minimization_evidence_original
    {originalWitness minimizedWitness omittedRedundant : Prop} :
    AyMCWMMinimizationEvidence
      originalWitness minimizedWitness omittedRedundant ->
    originalWitness :=
  fun h => ay_mcwm_conj_left h

theorem ay_mcwm_minimization_evidence_minimized
    {originalWitness minimizedWitness omittedRedundant : Prop} :
    AyMCWMMinimizationEvidence
      originalWitness minimizedWitness omittedRedundant ->
    minimizedWitness :=
  fun h => ay_mcwm_conj_left (ay_mcwm_conj_right h)

theorem ay_mcwm_minimization_evidence_omitted
    {originalWitness minimizedWitness omittedRedundant : Prop} :
    AyMCWMMinimizationEvidence
      originalWitness minimizedWitness omittedRedundant ->
    omittedRedundant :=
  fun h => ay_mcwm_conj_right (ay_mcwm_conj_right h)

theorem ay_mcwm_extension_defaults_intro
    {defaultAssignments extensionMap defaultsComplete : Prop} :
    defaultAssignments ->
    extensionMap ->
    defaultsComplete ->
    AyMCWMExtensionDefaults defaultAssignments extensionMap defaultsComplete :=
  fun hdefaults hmap hcomplete =>
    ay_mcwm_conj_intro hdefaults
      (ay_mcwm_conj_intro hmap hcomplete)

theorem ay_mcwm_extension_defaults_assignments
    {defaultAssignments extensionMap defaultsComplete : Prop} :
    AyMCWMExtensionDefaults defaultAssignments extensionMap defaultsComplete ->
    defaultAssignments :=
  fun h => ay_mcwm_conj_left h

theorem ay_mcwm_extension_defaults_map
    {defaultAssignments extensionMap defaultsComplete : Prop} :
    AyMCWMExtensionDefaults defaultAssignments extensionMap defaultsComplete ->
    extensionMap :=
  fun h => ay_mcwm_conj_left (ay_mcwm_conj_right h)

theorem ay_mcwm_extension_defaults_complete
    {defaultAssignments extensionMap defaultsComplete : Prop} :
    AyMCWMExtensionDefaults defaultAssignments extensionMap defaultsComplete ->
    defaultsComplete :=
  fun h => ay_mcwm_conj_right (ay_mcwm_conj_right h)

theorem ay_mcwm_frame_compatibility_intro
    {cubeFrame assumptionFrame refinementFrame : Prop} :
    cubeFrame ->
    assumptionFrame ->
    refinementFrame ->
    AyMCWMFrameCompatibility cubeFrame assumptionFrame refinementFrame :=
  fun hcube hassumption hrefinement =>
    ay_mcwm_conj_intro hcube
      (ay_mcwm_conj_intro hassumption hrefinement)

theorem ay_mcwm_frame_compatibility_cube
    {cubeFrame assumptionFrame refinementFrame : Prop} :
    AyMCWMFrameCompatibility cubeFrame assumptionFrame refinementFrame ->
    cubeFrame :=
  fun h => ay_mcwm_conj_left h

theorem ay_mcwm_frame_compatibility_assumption
    {cubeFrame assumptionFrame refinementFrame : Prop} :
    AyMCWMFrameCompatibility cubeFrame assumptionFrame refinementFrame ->
    assumptionFrame :=
  fun h => ay_mcwm_conj_left (ay_mcwm_conj_right h)

theorem ay_mcwm_frame_compatibility_refinement
    {cubeFrame assumptionFrame refinementFrame : Prop} :
    AyMCWMFrameCompatibility cubeFrame assumptionFrame refinementFrame ->
    refinementFrame :=
  fun h => ay_mcwm_conj_right (ay_mcwm_conj_right h)

theorem ay_mcwm_formula_fingerprint_intro
    {minimizedFingerprint originalFingerprint fingerprintAgreement : Prop} :
    minimizedFingerprint ->
    originalFingerprint ->
    fingerprintAgreement ->
    AyMCWMFormulaFingerprint
      minimizedFingerprint originalFingerprint fingerprintAgreement :=
  fun hminimized horiginal hagree =>
    ay_mcwm_conj_intro hminimized
      (ay_mcwm_conj_intro horiginal hagree)

theorem ay_mcwm_formula_fingerprint_minimized
    {minimizedFingerprint originalFingerprint fingerprintAgreement : Prop} :
    AyMCWMFormulaFingerprint
      minimizedFingerprint originalFingerprint fingerprintAgreement ->
    minimizedFingerprint :=
  fun h => ay_mcwm_conj_left h

theorem ay_mcwm_formula_fingerprint_original
    {minimizedFingerprint originalFingerprint fingerprintAgreement : Prop} :
    AyMCWMFormulaFingerprint
      minimizedFingerprint originalFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mcwm_conj_left (ay_mcwm_conj_right h)

theorem ay_mcwm_formula_fingerprint_agreement
    {minimizedFingerprint originalFingerprint fingerprintAgreement : Prop} :
    AyMCWMFormulaFingerprint
      minimizedFingerprint originalFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mcwm_conj_right (ay_mcwm_conj_right h)

theorem ay_mcwm_model_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMCWMModelCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mcwm_conj_intro haccepted htrace

theorem ay_mcwm_model_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMCWMModelCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_mcwm_conj_left h

theorem ay_mcwm_model_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMCWMModelCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_mcwm_conj_right h

theorem ay_mcwm_manifest_digest_intro
    {manifestEntry witnessDigest digestAgreement : Prop} :
    manifestEntry ->
    witnessDigest ->
    digestAgreement ->
    AyMCWMManifestDigest manifestEntry witnessDigest digestAgreement :=
  fun hmanifest hdigest hagree =>
    ay_mcwm_conj_intro hmanifest
      (ay_mcwm_conj_intro hdigest hagree)

theorem ay_mcwm_manifest_digest_entry
    {manifestEntry witnessDigest digestAgreement : Prop} :
    AyMCWMManifestDigest manifestEntry witnessDigest digestAgreement ->
    manifestEntry :=
  fun h => ay_mcwm_conj_left h

theorem ay_mcwm_manifest_digest_witness
    {manifestEntry witnessDigest digestAgreement : Prop} :
    AyMCWMManifestDigest manifestEntry witnessDigest digestAgreement ->
    witnessDigest :=
  fun h => ay_mcwm_conj_left (ay_mcwm_conj_right h)

theorem ay_mcwm_manifest_digest_agreement
    {manifestEntry witnessDigest digestAgreement : Prop} :
    AyMCWMManifestDigest manifestEntry witnessDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mcwm_conj_right (ay_mcwm_conj_right h)

theorem ay_mcwm_re_extension_apply
    {minimizedAssignment publicAssignment : Prop} :
    AyMCWMReExtension minimizedAssignment publicAssignment ->
    minimizedAssignment ->
    publicAssignment :=
  fun hextend hminimized => hextend hminimized

theorem ay_mcwm_publication_evidence_intro
    {minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk :
      Prop} :
    minimizationOk ->
    defaultsOk ->
    frameOk ->
    fingerprintOk ->
    checkerOk ->
    digestOk ->
    AyMCWMPublicationEvidence
      minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk :=
  fun hmin hdefaults hframe hfingerprint hchecker hdigest =>
    ay_mcwm_conj_intro hmin
      (ay_mcwm_conj_intro hdefaults
        (ay_mcwm_conj_intro hframe
          (ay_mcwm_conj_intro hfingerprint
            (ay_mcwm_conj_intro hchecker hdigest))))

theorem ay_mcwm_publication_evidence_minimization
    {minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk :
      Prop} :
    AyMCWMPublicationEvidence
      minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk ->
    minimizationOk :=
  fun h => ay_mcwm_conj_left h

theorem ay_mcwm_publication_evidence_defaults
    {minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk :
      Prop} :
    AyMCWMPublicationEvidence
      minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk ->
    defaultsOk :=
  fun h => ay_mcwm_conj_left (ay_mcwm_conj_right h)

theorem ay_mcwm_publication_evidence_frame
    {minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk :
      Prop} :
    AyMCWMPublicationEvidence
      minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk ->
    frameOk :=
  fun h => ay_mcwm_conj_left (ay_mcwm_conj_right (ay_mcwm_conj_right h))

theorem ay_mcwm_publication_evidence_fingerprint
    {minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk :
      Prop} :
    AyMCWMPublicationEvidence
      minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk ->
    fingerprintOk :=
  fun h =>
    ay_mcwm_conj_left
      (ay_mcwm_conj_right (ay_mcwm_conj_right (ay_mcwm_conj_right h)))

theorem ay_mcwm_publication_evidence_checker
    {minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk :
      Prop} :
    AyMCWMPublicationEvidence
      minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk ->
    checkerOk :=
  fun h =>
    ay_mcwm_conj_left
      (ay_mcwm_conj_right
        (ay_mcwm_conj_right (ay_mcwm_conj_right (ay_mcwm_conj_right h))))

theorem ay_mcwm_publication_evidence_digest
    {minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk :
      Prop} :
    AyMCWMPublicationEvidence
      minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk ->
    digestOk :=
  fun h =>
    ay_mcwm_conj_right
      (ay_mcwm_conj_right
        (ay_mcwm_conj_right (ay_mcwm_conj_right (ay_mcwm_conj_right h))))

theorem ay_mcwm_minimized_sat_publication_intro
    {publicationEvidence auditEntry publicSatModel : Prop} :
    publicationEvidence ->
    auditEntry ->
    publicSatModel ->
    AyMCWMMinimizedSatPublication
      publicationEvidence auditEntry publicSatModel :=
  fun hevidence haudit hmodel =>
    ay_mcwm_conj_intro hevidence (ay_mcwm_conj_intro haudit hmodel)

theorem ay_mcwm_minimized_sat_publication_evidence
    {publicationEvidence auditEntry publicSatModel : Prop} :
    AyMCWMMinimizedSatPublication
      publicationEvidence auditEntry publicSatModel ->
    publicationEvidence :=
  fun h => ay_mcwm_conj_left h

theorem ay_mcwm_minimized_sat_publication_audit
    {publicationEvidence auditEntry publicSatModel : Prop} :
    AyMCWMMinimizedSatPublication
      publicationEvidence auditEntry publicSatModel ->
    auditEntry :=
  fun h => ay_mcwm_conj_left (ay_mcwm_conj_right h)

theorem ay_mcwm_minimized_sat_publication_model
    {publicationEvidence auditEntry publicSatModel : Prop} :
    AyMCWMMinimizedSatPublication
      publicationEvidence auditEntry publicSatModel ->
    publicSatModel :=
  fun h => ay_mcwm_conj_right (ay_mcwm_conj_right h)

theorem ay_mcwm_accepted_minimization_preserves_sat_publication
    {publicationEvidence auditEntry publicSatModel : Prop} :
    AyMCWMMinimizedSatPublication
      publicationEvidence auditEntry publicSatModel ->
    publicSatModel :=
  fun h => ay_mcwm_minimized_sat_publication_model h

theorem ay_mcwm_minimized_publication_from_reextension
    {minimizedAssignment publicSatModel minimizationOk defaultsOk frameOk
      fingerprintOk checkerOk digestOk auditEntry : Prop} :
    AyMCWMReExtension minimizedAssignment publicSatModel ->
    minimizedAssignment ->
    minimizationOk ->
    defaultsOk ->
    frameOk ->
    fingerprintOk ->
    checkerOk ->
    digestOk ->
    auditEntry ->
    AyMCWMMinimizedSatPublication
      (AyMCWMPublicationEvidence
        minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk)
      auditEntry
      publicSatModel :=
  fun hextend hminimized hmin hdefaults hframe hfingerprint hchecker
      hdigest haudit =>
    ay_mcwm_minimized_sat_publication_intro
      (ay_mcwm_publication_evidence_intro
        hmin hdefaults hframe hfingerprint hchecker hdigest)
      haudit
      (hextend hminimized)

theorem ay_mcwm_publication_requires_minimization
    {minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk
      auditEntry publicSatModel : Prop} :
    AyMCWMMinimizedSatPublication
      (AyMCWMPublicationEvidence
        minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk)
      auditEntry
      publicSatModel ->
    minimizationOk :=
  fun h =>
    ay_mcwm_publication_evidence_minimization
      (ay_mcwm_minimized_sat_publication_evidence h)

theorem ay_mcwm_publication_requires_defaults
    {minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk
      auditEntry publicSatModel : Prop} :
    AyMCWMMinimizedSatPublication
      (AyMCWMPublicationEvidence
        minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk)
      auditEntry
      publicSatModel ->
    defaultsOk :=
  fun h =>
    ay_mcwm_publication_evidence_defaults
      (ay_mcwm_minimized_sat_publication_evidence h)

theorem ay_mcwm_publication_requires_frame
    {minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk
      auditEntry publicSatModel : Prop} :
    AyMCWMMinimizedSatPublication
      (AyMCWMPublicationEvidence
        minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk)
      auditEntry
      publicSatModel ->
    frameOk :=
  fun h =>
    ay_mcwm_publication_evidence_frame
      (ay_mcwm_minimized_sat_publication_evidence h)

theorem ay_mcwm_publication_requires_fingerprint
    {minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk
      auditEntry publicSatModel : Prop} :
    AyMCWMMinimizedSatPublication
      (AyMCWMPublicationEvidence
        minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk)
      auditEntry
      publicSatModel ->
    fingerprintOk :=
  fun h =>
    ay_mcwm_publication_evidence_fingerprint
      (ay_mcwm_minimized_sat_publication_evidence h)

theorem ay_mcwm_publication_requires_checker
    {minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk
      auditEntry publicSatModel : Prop} :
    AyMCWMMinimizedSatPublication
      (AyMCWMPublicationEvidence
        minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk)
      auditEntry
      publicSatModel ->
    checkerOk :=
  fun h =>
    ay_mcwm_publication_evidence_checker
      (ay_mcwm_minimized_sat_publication_evidence h)

theorem ay_mcwm_publication_requires_digest
    {minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk
      auditEntry publicSatModel : Prop} :
    AyMCWMMinimizedSatPublication
      (AyMCWMPublicationEvidence
        minimizationOk defaultsOk frameOk fingerprintOk checkerOk digestOk)
      auditEntry
      publicSatModel ->
    digestOk :=
  fun h =>
    ay_mcwm_publication_evidence_digest
      (ay_mcwm_minimized_sat_publication_evidence h)

theorem ay_mcwm_minimized_sat_publication_sound_exact
    {publicationEvidence auditEntry publicSatModel : Prop} :
    AyMCWMEquisat
      (AyMCWMMinimizedSatPublication
        publicationEvidence auditEntry publicSatModel)
      (AyMCWMConj publicationEvidence
        (AyMCWMConj auditEntry publicSatModel)) :=
  ay_mcwm_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_mcwm_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMCWMNoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_mcwm_conj_intro hdiagnostic hblocks

theorem ay_mcwm_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMCWMNoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_mcwm_conj_left h

theorem ay_mcwm_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMCWMNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_mcwm_conj_right h

theorem ay_mcwm_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMCWMRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_mcwm_conj_intro hreason hrequest

theorem ay_mcwm_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMCWMRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_mcwm_conj_left h

theorem ay_mcwm_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMCWMRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_mcwm_conj_right h

theorem ay_mcwm_stale_minimization_recompute
    {staleMinimization recomputeRequest : Prop} :
    staleMinimization ->
    recomputeRequest ->
    AyMCWMRecomputeObligation staleMinimization recomputeRequest :=
  fun hstale hrecompute =>
    ay_mcwm_recompute_obligation_intro hstale hrecompute

theorem ay_mcwm_stale_minimization_no_claim
    {staleMinimization publicClaim : Prop} :
    staleMinimization ->
    (staleMinimization -> publicClaim -> False) ->
    AyMCWMNoClaimDiagnostic staleMinimization publicClaim :=
  fun hstale hblocks =>
    ay_mcwm_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_mcwm_missing_defaults_no_claim
    {missingDefaults publicClaim : Prop} :
    missingDefaults ->
    (missingDefaults -> publicClaim -> False) ->
    AyMCWMNoClaimDiagnostic missingDefaults publicClaim :=
  fun hmissing hblocks =>
    ay_mcwm_no_claim_diagnostic_intro hmissing (hblocks hmissing)

theorem ay_mcwm_frame_mismatch_no_claim
    {frameMismatch publicClaim : Prop} :
    frameMismatch ->
    (frameMismatch -> publicClaim -> False) ->
    AyMCWMNoClaimDiagnostic frameMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mcwm_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mcwm_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicClaim : Prop} :
    fingerprintMismatch ->
    (fingerprintMismatch -> publicClaim -> False) ->
    AyMCWMNoClaimDiagnostic fingerprintMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mcwm_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mcwm_digest_mismatch_no_claim
    {digestMismatch publicClaim : Prop} :
    digestMismatch ->
    (digestMismatch -> publicClaim -> False) ->
    AyMCWMNoClaimDiagnostic digestMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mcwm_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mcwm_checker_rejection_no_claim
    {checkerRejection publicClaim : Prop} :
    checkerRejection ->
    (checkerRejection -> publicClaim -> False) ->
    AyMCWMNoClaimDiagnostic checkerRejection publicClaim :=
  fun hreject hblocks =>
    ay_mcwm_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_mcwm_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMCWMNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_mcwm_no_claim_diagnostic_blocks h hclaim

theorem ay_mcwm_bad_minimization_no_stale_sat_publication
    {staleMinimization missingDefaults frameMismatch fingerprintMismatch
      digestMismatch checkerRejection publicClaim : Prop} :
    (staleMinimization -> publicClaim -> False) ->
    (missingDefaults -> publicClaim -> False) ->
    (frameMismatch -> publicClaim -> False) ->
    (fingerprintMismatch -> publicClaim -> False) ->
    (digestMismatch -> publicClaim -> False) ->
    (checkerRejection -> publicClaim -> False) ->
    AyMCWMConj
      (staleMinimization ->
        AyMCWMNoClaimDiagnostic staleMinimization publicClaim)
      (AyMCWMConj
        (missingDefaults ->
          AyMCWMNoClaimDiagnostic missingDefaults publicClaim)
        (AyMCWMConj
          (frameMismatch ->
            AyMCWMNoClaimDiagnostic frameMismatch publicClaim)
          (AyMCWMConj
            (fingerprintMismatch ->
              AyMCWMNoClaimDiagnostic fingerprintMismatch publicClaim)
            (AyMCWMConj
              (digestMismatch ->
                AyMCWMNoClaimDiagnostic digestMismatch publicClaim)
              (checkerRejection ->
                AyMCWMNoClaimDiagnostic checkerRejection publicClaim))))) :=
  fun hmin hdefaults hframe hfingerprint hdigest hchecker =>
    ay_mcwm_conj_intro
      (fun h => ay_mcwm_stale_minimization_no_claim h hmin)
      (ay_mcwm_conj_intro
        (fun h => ay_mcwm_missing_defaults_no_claim h hdefaults)
        (ay_mcwm_conj_intro
          (fun h => ay_mcwm_frame_mismatch_no_claim h hframe)
          (ay_mcwm_conj_intro
            (fun h => ay_mcwm_fingerprint_mismatch_no_claim h hfingerprint)
            (ay_mcwm_conj_intro
              (fun h => ay_mcwm_digest_mismatch_no_claim h hdigest)
              (fun h => ay_mcwm_checker_rejection_no_claim h hchecker)))))
