-- SAT-COMP/ay public assignment canonicalization soundness skeleton.
-- A reconstructed model may be canonicalized for SAT-COMP output only when
-- ordering, eliminated defaults, frame/fingerprint agreement, replay, and
-- manifest digest evidence agree.

def AyMPACConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMPACDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMPACEquisat (left right : Prop) : Prop :=
  AyMPACConj (left -> right) (right -> left)

def AyMPACVariableOrdering
    (visibleOrder canonicalOrder orderingStable : Prop) : Prop :=
  AyMPACConj visibleOrder (AyMPACConj canonicalOrder orderingStable)

def AyMPACEliminatedDefaults
    (eliminatedVariables defaultAssignments defaultsComplete : Prop) : Prop :=
  AyMPACConj eliminatedVariables
    (AyMPACConj defaultAssignments defaultsComplete)

def AyMPACFrameCompatibility
    (preprocessFrame refinementFrame outputFrame : Prop) : Prop :=
  AyMPACConj preprocessFrame (AyMPACConj refinementFrame outputFrame)

def AyMPACFormulaFingerprint
    (reconstructedFingerprint originalFingerprint fingerprintAgreement :
      Prop) : Prop :=
  AyMPACConj reconstructedFingerprint
    (AyMPACConj originalFingerprint fingerprintAgreement)

def AyMPACModelCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMPACConj checkerAccepted replayTrace

def AyMPACManifestDigest
    (manifestId assignmentDigest digestAgreement : Prop) : Prop :=
  AyMPACConj manifestId (AyMPACConj assignmentDigest digestAgreement)

def AyMPACCanonicalizationEvidence
    (orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk : Prop) :
    Prop :=
  AyMPACConj orderingOk
    (AyMPACConj defaultsOk
      (AyMPACConj frameOk
        (AyMPACConj fingerprintOk
          (AyMPACConj checkerOk digestOk))))

def AyMPACCanonicalSatPublication
    (canonicalizationEvidence auditEntry publicSatModel : Prop) : Prop :=
  AyMPACConj canonicalizationEvidence
    (AyMPACConj auditEntry publicSatModel)

def AyMPACNoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMPACConj diagnostic (publicClaim -> False)

def AyMPACRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMPACConj reason recomputeRequest

theorem ay_mpac_conj_intro {left right : Prop} :
    left -> right -> AyMPACConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mpac_conj_left {left right : Prop} :
    AyMPACConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mpac_conj_right {left right : Prop} :
    AyMPACConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mpac_disj_left {left right : Prop} :
    left -> AyMPACDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mpac_disj_right {left right : Prop} :
    right -> AyMPACDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mpac_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMPACEquisat left right :=
  fun hf hb => ay_mpac_conj_intro hf hb

theorem ay_mpac_equisat_forward {left right : Prop} :
    AyMPACEquisat left right -> left -> right :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_equisat_backward {left right : Prop} :
    AyMPACEquisat left right -> right -> left :=
  fun h => ay_mpac_conj_right h

theorem ay_mpac_variable_ordering_intro
    {visibleOrder canonicalOrder orderingStable : Prop} :
    visibleOrder ->
    canonicalOrder ->
    orderingStable ->
    AyMPACVariableOrdering visibleOrder canonicalOrder orderingStable :=
  fun hvisible hcanonical hstable =>
    ay_mpac_conj_intro hvisible
      (ay_mpac_conj_intro hcanonical hstable)

theorem ay_mpac_variable_ordering_visible
    {visibleOrder canonicalOrder orderingStable : Prop} :
    AyMPACVariableOrdering visibleOrder canonicalOrder orderingStable ->
    visibleOrder :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_variable_ordering_canonical
    {visibleOrder canonicalOrder orderingStable : Prop} :
    AyMPACVariableOrdering visibleOrder canonicalOrder orderingStable ->
    canonicalOrder :=
  fun h => ay_mpac_conj_left (ay_mpac_conj_right h)

theorem ay_mpac_variable_ordering_stable
    {visibleOrder canonicalOrder orderingStable : Prop} :
    AyMPACVariableOrdering visibleOrder canonicalOrder orderingStable ->
    orderingStable :=
  fun h => ay_mpac_conj_right (ay_mpac_conj_right h)

theorem ay_mpac_eliminated_defaults_intro
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    eliminatedVariables ->
    defaultAssignments ->
    defaultsComplete ->
    AyMPACEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete :=
  fun helim hdefaults hcomplete =>
    ay_mpac_conj_intro helim
      (ay_mpac_conj_intro hdefaults hcomplete)

theorem ay_mpac_eliminated_defaults_variables
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMPACEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    eliminatedVariables :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_eliminated_defaults_assignments
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMPACEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    defaultAssignments :=
  fun h => ay_mpac_conj_left (ay_mpac_conj_right h)

theorem ay_mpac_eliminated_defaults_complete
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMPACEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    defaultsComplete :=
  fun h => ay_mpac_conj_right (ay_mpac_conj_right h)

theorem ay_mpac_frame_compatibility_intro
    {preprocessFrame refinementFrame outputFrame : Prop} :
    preprocessFrame ->
    refinementFrame ->
    outputFrame ->
    AyMPACFrameCompatibility preprocessFrame refinementFrame outputFrame :=
  fun hpre hrefine hout =>
    ay_mpac_conj_intro hpre (ay_mpac_conj_intro hrefine hout)

theorem ay_mpac_frame_compatibility_preprocess
    {preprocessFrame refinementFrame outputFrame : Prop} :
    AyMPACFrameCompatibility preprocessFrame refinementFrame outputFrame ->
    preprocessFrame :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_frame_compatibility_refinement
    {preprocessFrame refinementFrame outputFrame : Prop} :
    AyMPACFrameCompatibility preprocessFrame refinementFrame outputFrame ->
    refinementFrame :=
  fun h => ay_mpac_conj_left (ay_mpac_conj_right h)

theorem ay_mpac_frame_compatibility_output
    {preprocessFrame refinementFrame outputFrame : Prop} :
    AyMPACFrameCompatibility preprocessFrame refinementFrame outputFrame ->
    outputFrame :=
  fun h => ay_mpac_conj_right (ay_mpac_conj_right h)

theorem ay_mpac_formula_fingerprint_intro
    {reconstructedFingerprint originalFingerprint fingerprintAgreement :
      Prop} :
    reconstructedFingerprint ->
    originalFingerprint ->
    fingerprintAgreement ->
    AyMPACFormulaFingerprint
      reconstructedFingerprint originalFingerprint fingerprintAgreement :=
  fun hreconstructed horiginal hagree =>
    ay_mpac_conj_intro hreconstructed
      (ay_mpac_conj_intro horiginal hagree)

theorem ay_mpac_formula_fingerprint_reconstructed
    {reconstructedFingerprint originalFingerprint fingerprintAgreement :
      Prop} :
    AyMPACFormulaFingerprint
      reconstructedFingerprint originalFingerprint fingerprintAgreement ->
    reconstructedFingerprint :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_formula_fingerprint_original
    {reconstructedFingerprint originalFingerprint fingerprintAgreement :
      Prop} :
    AyMPACFormulaFingerprint
      reconstructedFingerprint originalFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mpac_conj_left (ay_mpac_conj_right h)

theorem ay_mpac_formula_fingerprint_agreement
    {reconstructedFingerprint originalFingerprint fingerprintAgreement :
      Prop} :
    AyMPACFormulaFingerprint
      reconstructedFingerprint originalFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mpac_conj_right (ay_mpac_conj_right h)

theorem ay_mpac_model_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMPACModelCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mpac_conj_intro haccepted htrace

theorem ay_mpac_model_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMPACModelCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_model_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMPACModelCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_mpac_conj_right h

theorem ay_mpac_manifest_digest_intro
    {manifestId assignmentDigest digestAgreement : Prop} :
    manifestId ->
    assignmentDigest ->
    digestAgreement ->
    AyMPACManifestDigest manifestId assignmentDigest digestAgreement :=
  fun hmanifest hdigest hagree =>
    ay_mpac_conj_intro hmanifest
      (ay_mpac_conj_intro hdigest hagree)

theorem ay_mpac_manifest_digest_manifest
    {manifestId assignmentDigest digestAgreement : Prop} :
    AyMPACManifestDigest manifestId assignmentDigest digestAgreement ->
    manifestId :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_manifest_digest_assignment
    {manifestId assignmentDigest digestAgreement : Prop} :
    AyMPACManifestDigest manifestId assignmentDigest digestAgreement ->
    assignmentDigest :=
  fun h => ay_mpac_conj_left (ay_mpac_conj_right h)

theorem ay_mpac_manifest_digest_agreement
    {manifestId assignmentDigest digestAgreement : Prop} :
    AyMPACManifestDigest manifestId assignmentDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mpac_conj_right (ay_mpac_conj_right h)

theorem ay_mpac_canonicalization_evidence_intro
    {orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk : Prop} :
    orderingOk ->
    defaultsOk ->
    frameOk ->
    fingerprintOk ->
    checkerOk ->
    digestOk ->
    AyMPACCanonicalizationEvidence
      orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk :=
  fun horder hdefaults hframe hfingerprint hchecker hdigest =>
    ay_mpac_conj_intro horder
      (ay_mpac_conj_intro hdefaults
        (ay_mpac_conj_intro hframe
          (ay_mpac_conj_intro hfingerprint
            (ay_mpac_conj_intro hchecker hdigest))))

theorem ay_mpac_canonicalization_evidence_ordering
    {orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk : Prop} :
    AyMPACCanonicalizationEvidence
      orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk ->
    orderingOk :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_canonicalization_evidence_defaults
    {orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk : Prop} :
    AyMPACCanonicalizationEvidence
      orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk ->
    defaultsOk :=
  fun h => ay_mpac_conj_left (ay_mpac_conj_right h)

theorem ay_mpac_canonicalization_evidence_frame
    {orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk : Prop} :
    AyMPACCanonicalizationEvidence
      orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk ->
    frameOk :=
  fun h => ay_mpac_conj_left (ay_mpac_conj_right (ay_mpac_conj_right h))

theorem ay_mpac_canonicalization_evidence_fingerprint
    {orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk : Prop} :
    AyMPACCanonicalizationEvidence
      orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk ->
    fingerprintOk :=
  fun h =>
    ay_mpac_conj_left
      (ay_mpac_conj_right (ay_mpac_conj_right (ay_mpac_conj_right h)))

theorem ay_mpac_canonicalization_evidence_checker
    {orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk : Prop} :
    AyMPACCanonicalizationEvidence
      orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk ->
    checkerOk :=
  fun h =>
    ay_mpac_conj_left
      (ay_mpac_conj_right
        (ay_mpac_conj_right (ay_mpac_conj_right (ay_mpac_conj_right h))))

theorem ay_mpac_canonicalization_evidence_digest
    {orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk : Prop} :
    AyMPACCanonicalizationEvidence
      orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk ->
    digestOk :=
  fun h =>
    ay_mpac_conj_right
      (ay_mpac_conj_right
        (ay_mpac_conj_right (ay_mpac_conj_right (ay_mpac_conj_right h))))

theorem ay_mpac_canonical_sat_publication_intro
    {canonicalizationEvidence auditEntry publicSatModel : Prop} :
    canonicalizationEvidence ->
    auditEntry ->
    publicSatModel ->
    AyMPACCanonicalSatPublication
      canonicalizationEvidence auditEntry publicSatModel :=
  fun hevidence haudit hmodel =>
    ay_mpac_conj_intro hevidence (ay_mpac_conj_intro haudit hmodel)

theorem ay_mpac_canonical_sat_publication_evidence
    {canonicalizationEvidence auditEntry publicSatModel : Prop} :
    AyMPACCanonicalSatPublication
      canonicalizationEvidence auditEntry publicSatModel ->
    canonicalizationEvidence :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_canonical_sat_publication_audit
    {canonicalizationEvidence auditEntry publicSatModel : Prop} :
    AyMPACCanonicalSatPublication
      canonicalizationEvidence auditEntry publicSatModel ->
    auditEntry :=
  fun h => ay_mpac_conj_left (ay_mpac_conj_right h)

theorem ay_mpac_canonical_sat_publication_model
    {canonicalizationEvidence auditEntry publicSatModel : Prop} :
    AyMPACCanonicalSatPublication
      canonicalizationEvidence auditEntry publicSatModel ->
    publicSatModel :=
  fun h => ay_mpac_conj_right (ay_mpac_conj_right h)

theorem ay_mpac_accepted_canonicalization_preserves_sat_publication
    {canonicalizationEvidence auditEntry publicSatModel : Prop} :
    AyMPACCanonicalSatPublication
      canonicalizationEvidence auditEntry publicSatModel ->
    publicSatModel :=
  fun h => ay_mpac_canonical_sat_publication_model h

theorem ay_mpac_publication_requires_ordering
    {orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk auditEntry
      publicSatModel : Prop} :
    AyMPACCanonicalSatPublication
      (AyMPACCanonicalizationEvidence
        orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk)
      auditEntry
      publicSatModel ->
    orderingOk :=
  fun h =>
    ay_mpac_canonicalization_evidence_ordering
      (ay_mpac_canonical_sat_publication_evidence h)

theorem ay_mpac_publication_requires_defaults
    {orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk auditEntry
      publicSatModel : Prop} :
    AyMPACCanonicalSatPublication
      (AyMPACCanonicalizationEvidence
        orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk)
      auditEntry
      publicSatModel ->
    defaultsOk :=
  fun h =>
    ay_mpac_canonicalization_evidence_defaults
      (ay_mpac_canonical_sat_publication_evidence h)

theorem ay_mpac_publication_requires_frame
    {orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk auditEntry
      publicSatModel : Prop} :
    AyMPACCanonicalSatPublication
      (AyMPACCanonicalizationEvidence
        orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk)
      auditEntry
      publicSatModel ->
    frameOk :=
  fun h =>
    ay_mpac_canonicalization_evidence_frame
      (ay_mpac_canonical_sat_publication_evidence h)

theorem ay_mpac_publication_requires_fingerprint
    {orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk auditEntry
      publicSatModel : Prop} :
    AyMPACCanonicalSatPublication
      (AyMPACCanonicalizationEvidence
        orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk)
      auditEntry
      publicSatModel ->
    fingerprintOk :=
  fun h =>
    ay_mpac_canonicalization_evidence_fingerprint
      (ay_mpac_canonical_sat_publication_evidence h)

theorem ay_mpac_publication_requires_checker
    {orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk auditEntry
      publicSatModel : Prop} :
    AyMPACCanonicalSatPublication
      (AyMPACCanonicalizationEvidence
        orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk)
      auditEntry
      publicSatModel ->
    checkerOk :=
  fun h =>
    ay_mpac_canonicalization_evidence_checker
      (ay_mpac_canonical_sat_publication_evidence h)

theorem ay_mpac_publication_requires_digest
    {orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk auditEntry
      publicSatModel : Prop} :
    AyMPACCanonicalSatPublication
      (AyMPACCanonicalizationEvidence
        orderingOk defaultsOk frameOk fingerprintOk checkerOk digestOk)
      auditEntry
      publicSatModel ->
    digestOk :=
  fun h =>
    ay_mpac_canonicalization_evidence_digest
      (ay_mpac_canonical_sat_publication_evidence h)

theorem ay_mpac_canonical_sat_publication_sound_exact
    {canonicalizationEvidence auditEntry publicSatModel : Prop} :
    AyMPACEquisat
      (AyMPACCanonicalSatPublication
        canonicalizationEvidence auditEntry publicSatModel)
      (AyMPACConj canonicalizationEvidence
        (AyMPACConj auditEntry publicSatModel)) :=
  ay_mpac_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_mpac_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMPACNoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_mpac_conj_intro hdiagnostic hblocks

theorem ay_mpac_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMPACNoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMPACNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_mpac_conj_right h

theorem ay_mpac_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMPACRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_mpac_conj_intro hreason hrequest

theorem ay_mpac_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMPACRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMPACRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_mpac_conj_right h

theorem ay_mpac_stale_ordering_recompute
    {staleOrdering recomputeRequest : Prop} :
    staleOrdering ->
    recomputeRequest ->
    AyMPACRecomputeObligation staleOrdering recomputeRequest :=
  fun hstale hrecompute =>
    ay_mpac_recompute_obligation_intro hstale hrecompute

theorem ay_mpac_stale_ordering_no_claim
    {staleOrdering publicClaim : Prop} :
    staleOrdering ->
    (staleOrdering -> publicClaim -> False) ->
    AyMPACNoClaimDiagnostic staleOrdering publicClaim :=
  fun hstale hblocks =>
    ay_mpac_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_mpac_missing_eliminated_defaults_no_claim
    {missingEliminatedDefaults publicClaim : Prop} :
    missingEliminatedDefaults ->
    (missingEliminatedDefaults -> publicClaim -> False) ->
    AyMPACNoClaimDiagnostic missingEliminatedDefaults publicClaim :=
  fun hmissing hblocks =>
    ay_mpac_no_claim_diagnostic_intro hmissing (hblocks hmissing)

theorem ay_mpac_frame_mismatch_no_claim
    {frameMismatch publicClaim : Prop} :
    frameMismatch ->
    (frameMismatch -> publicClaim -> False) ->
    AyMPACNoClaimDiagnostic frameMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mpac_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mpac_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicClaim : Prop} :
    fingerprintMismatch ->
    (fingerprintMismatch -> publicClaim -> False) ->
    AyMPACNoClaimDiagnostic fingerprintMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mpac_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mpac_digest_mismatch_no_claim
    {digestMismatch publicClaim : Prop} :
    digestMismatch ->
    (digestMismatch -> publicClaim -> False) ->
    AyMPACNoClaimDiagnostic digestMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mpac_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mpac_checker_rejection_no_claim
    {checkerRejection publicClaim : Prop} :
    checkerRejection ->
    (checkerRejection -> publicClaim -> False) ->
    AyMPACNoClaimDiagnostic checkerRejection publicClaim :=
  fun hreject hblocks =>
    ay_mpac_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_mpac_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMPACNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_mpac_no_claim_diagnostic_blocks h hclaim

theorem ay_mpac_bad_canonicalization_no_stale_sat_publication
    {staleOrdering missingEliminatedDefaults frameMismatch
      fingerprintMismatch digestMismatch checkerRejection publicClaim : Prop} :
    (staleOrdering -> publicClaim -> False) ->
    (missingEliminatedDefaults -> publicClaim -> False) ->
    (frameMismatch -> publicClaim -> False) ->
    (fingerprintMismatch -> publicClaim -> False) ->
    (digestMismatch -> publicClaim -> False) ->
    (checkerRejection -> publicClaim -> False) ->
    AyMPACConj
      (staleOrdering ->
        AyMPACNoClaimDiagnostic staleOrdering publicClaim)
      (AyMPACConj
        (missingEliminatedDefaults ->
          AyMPACNoClaimDiagnostic missingEliminatedDefaults publicClaim)
        (AyMPACConj
          (frameMismatch ->
            AyMPACNoClaimDiagnostic frameMismatch publicClaim)
          (AyMPACConj
            (fingerprintMismatch ->
              AyMPACNoClaimDiagnostic fingerprintMismatch publicClaim)
            (AyMPACConj
              (digestMismatch ->
                AyMPACNoClaimDiagnostic digestMismatch publicClaim)
              (checkerRejection ->
                AyMPACNoClaimDiagnostic checkerRejection publicClaim))))) :=
  fun horder hdefaults hframe hfingerprint hdigest hchecker =>
    ay_mpac_conj_intro
      (fun h => ay_mpac_stale_ordering_no_claim h horder)
      (ay_mpac_conj_intro
        (fun h => ay_mpac_missing_eliminated_defaults_no_claim h hdefaults)
        (ay_mpac_conj_intro
          (fun h => ay_mpac_frame_mismatch_no_claim h hframe)
          (ay_mpac_conj_intro
            (fun h => ay_mpac_fingerprint_mismatch_no_claim h hfingerprint)
            (ay_mpac_conj_intro
              (fun h => ay_mpac_digest_mismatch_no_claim h hdigest)
              (fun h => ay_mpac_checker_rejection_no_claim h hchecker)))))
