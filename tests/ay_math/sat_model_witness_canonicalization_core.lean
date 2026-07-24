-- SAT-COMP/ay witness canonicalization soundness skeleton.
-- Reordering, compressing, or canonicalizing a public SAT model witness is
-- admissible only under stable variable order, digest, reconstruction, map,
-- checker, build, and original-instance fingerprint evidence.

def AyMWCAConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMWCADisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMWCAEquisat (left right : Prop) : Prop :=
  AyMWCAConj (left -> right) (right -> left)

def AyMWCAVariableOrder
    (declaredOrder canonicalOrder noDuplicates domainComplete : Prop) : Prop :=
  AyMWCAConj declaredOrder
    (AyMWCAConj canonicalOrder
      (AyMWCAConj noDuplicates domainComplete))

def AyMWCAAssignmentDigest
    (sourceDigest canonicalDigest digestAgreement : Prop) : Prop :=
  AyMWCAConj sourceDigest
    (AyMWCAConj canonicalDigest digestAgreement)

def AyMWCAEliminatedReconstruction
    (eliminatedDefaults reconstructedValues reconstructionAgreement : Prop) :
    Prop :=
  AyMWCAConj eliminatedDefaults
    (AyMWCAConj reconstructedValues reconstructionAgreement)

def AyMWCAProjectionMap
    (solverMap originalMap mapAgreement : Prop) : Prop :=
  AyMWCAConj solverMap (AyMWCAConj originalMap mapAgreement)

def AyMWCACheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMWCAConj checkerAccepted replayTrace

def AyMWCASolverBuild (buildId witnessBuild buildAgreement : Prop) : Prop :=
  AyMWCAConj buildId (AyMWCAConj witnessBuild buildAgreement)

def AyMWCAOriginalFingerprint
    (originalFingerprint witnessFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMWCAConj originalFingerprint
    (AyMWCAConj witnessFingerprint fingerprintAgreement)

def AyMWCACanonicalizationEvidence
    (orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk : Prop) : Prop :=
  AyMWCAConj orderOk
    (AyMWCAConj digestOk
      (AyMWCAConj reconstructionOk
        (AyMWCAConj mapOk
          (AyMWCAConj replayOk
            (AyMWCAConj buildOk fingerprintOk)))))

def AyMWCAPublicSatResult
    (canonicalEvidence canonicalWitness publicSatClaim : Prop) : Prop :=
  AyMWCAConj canonicalEvidence
    (AyMWCAConj canonicalWitness publicSatClaim)

def AyMWCANoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMWCAConj diagnostic (publicSatClaim -> False)

def AyMWCARecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMWCAConj reason recomputeRequest

theorem ay_mwca_conj_intro {left right : Prop} :
    left -> right -> AyMWCAConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mwca_conj_left {left right : Prop} :
    AyMWCAConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mwca_conj_right {left right : Prop} :
    AyMWCAConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mwca_disj_left {left right : Prop} :
    left -> AyMWCADisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mwca_disj_right {left right : Prop} :
    right -> AyMWCADisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mwca_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMWCAEquisat left right :=
  fun hf hb => ay_mwca_conj_intro hf hb

theorem ay_mwca_equisat_forward {left right : Prop} :
    AyMWCAEquisat left right -> left -> right :=
  fun h => ay_mwca_conj_left h

theorem ay_mwca_equisat_backward {left right : Prop} :
    AyMWCAEquisat left right -> right -> left :=
  fun h => ay_mwca_conj_right h

theorem ay_mwca_variable_order_intro
    {declaredOrder canonicalOrder noDuplicates domainComplete : Prop} :
    declaredOrder ->
    canonicalOrder ->
    noDuplicates ->
    domainComplete ->
    AyMWCAVariableOrder
      declaredOrder canonicalOrder noDuplicates domainComplete :=
  fun hdeclared hcanonical hnodup hcomplete =>
    ay_mwca_conj_intro hdeclared
      (ay_mwca_conj_intro hcanonical
        (ay_mwca_conj_intro hnodup hcomplete))

theorem ay_mwca_variable_order_declared
    {declaredOrder canonicalOrder noDuplicates domainComplete : Prop} :
    AyMWCAVariableOrder
      declaredOrder canonicalOrder noDuplicates domainComplete ->
    declaredOrder :=
  fun h => ay_mwca_conj_left h

theorem ay_mwca_variable_order_canonical
    {declaredOrder canonicalOrder noDuplicates domainComplete : Prop} :
    AyMWCAVariableOrder
      declaredOrder canonicalOrder noDuplicates domainComplete ->
    canonicalOrder :=
  fun h => ay_mwca_conj_left (ay_mwca_conj_right h)

theorem ay_mwca_variable_order_no_duplicates
    {declaredOrder canonicalOrder noDuplicates domainComplete : Prop} :
    AyMWCAVariableOrder
      declaredOrder canonicalOrder noDuplicates domainComplete ->
    noDuplicates :=
  fun h => ay_mwca_conj_left
    (ay_mwca_conj_right (ay_mwca_conj_right h))

theorem ay_mwca_variable_order_domain_complete
    {declaredOrder canonicalOrder noDuplicates domainComplete : Prop} :
    AyMWCAVariableOrder
      declaredOrder canonicalOrder noDuplicates domainComplete ->
    domainComplete :=
  fun h => ay_mwca_conj_right
    (ay_mwca_conj_right (ay_mwca_conj_right h))

theorem ay_mwca_assignment_digest_intro
    {sourceDigest canonicalDigest digestAgreement : Prop} :
    sourceDigest ->
    canonicalDigest ->
    digestAgreement ->
    AyMWCAAssignmentDigest
      sourceDigest canonicalDigest digestAgreement :=
  fun hsource hcanonical hagree =>
    ay_mwca_conj_intro hsource
      (ay_mwca_conj_intro hcanonical hagree)

theorem ay_mwca_assignment_digest_source
    {sourceDigest canonicalDigest digestAgreement : Prop} :
    AyMWCAAssignmentDigest
      sourceDigest canonicalDigest digestAgreement ->
    sourceDigest :=
  fun h => ay_mwca_conj_left h

theorem ay_mwca_assignment_digest_canonical
    {sourceDigest canonicalDigest digestAgreement : Prop} :
    AyMWCAAssignmentDigest
      sourceDigest canonicalDigest digestAgreement ->
    canonicalDigest :=
  fun h => ay_mwca_conj_left (ay_mwca_conj_right h)

theorem ay_mwca_assignment_digest_agreement
    {sourceDigest canonicalDigest digestAgreement : Prop} :
    AyMWCAAssignmentDigest
      sourceDigest canonicalDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mwca_conj_right (ay_mwca_conj_right h)

theorem ay_mwca_eliminated_reconstruction_intro
    {eliminatedDefaults reconstructedValues reconstructionAgreement : Prop} :
    eliminatedDefaults ->
    reconstructedValues ->
    reconstructionAgreement ->
    AyMWCAEliminatedReconstruction
      eliminatedDefaults reconstructedValues reconstructionAgreement :=
  fun hdefaults hvalues hagree =>
    ay_mwca_conj_intro hdefaults
      (ay_mwca_conj_intro hvalues hagree)

theorem ay_mwca_eliminated_reconstruction_defaults
    {eliminatedDefaults reconstructedValues reconstructionAgreement : Prop} :
    AyMWCAEliminatedReconstruction
      eliminatedDefaults reconstructedValues reconstructionAgreement ->
    eliminatedDefaults :=
  fun h => ay_mwca_conj_left h

theorem ay_mwca_eliminated_reconstruction_values
    {eliminatedDefaults reconstructedValues reconstructionAgreement : Prop} :
    AyMWCAEliminatedReconstruction
      eliminatedDefaults reconstructedValues reconstructionAgreement ->
    reconstructedValues :=
  fun h => ay_mwca_conj_left (ay_mwca_conj_right h)

theorem ay_mwca_eliminated_reconstruction_agreement
    {eliminatedDefaults reconstructedValues reconstructionAgreement : Prop} :
    AyMWCAEliminatedReconstruction
      eliminatedDefaults reconstructedValues reconstructionAgreement ->
    reconstructionAgreement :=
  fun h => ay_mwca_conj_right (ay_mwca_conj_right h)

theorem ay_mwca_projection_map_intro
    {solverMap originalMap mapAgreement : Prop} :
    solverMap ->
    originalMap ->
    mapAgreement ->
    AyMWCAProjectionMap solverMap originalMap mapAgreement :=
  fun hsolver horiginal hagree =>
    ay_mwca_conj_intro hsolver
      (ay_mwca_conj_intro horiginal hagree)

theorem ay_mwca_projection_map_solver
    {solverMap originalMap mapAgreement : Prop} :
    AyMWCAProjectionMap solverMap originalMap mapAgreement -> solverMap :=
  fun h => ay_mwca_conj_left h

theorem ay_mwca_projection_map_original
    {solverMap originalMap mapAgreement : Prop} :
    AyMWCAProjectionMap solverMap originalMap mapAgreement -> originalMap :=
  fun h => ay_mwca_conj_left (ay_mwca_conj_right h)

theorem ay_mwca_projection_map_agreement
    {solverMap originalMap mapAgreement : Prop} :
    AyMWCAProjectionMap solverMap originalMap mapAgreement -> mapAgreement :=
  fun h => ay_mwca_conj_right (ay_mwca_conj_right h)

theorem ay_mwca_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMWCACheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mwca_conj_intro haccepted htrace

theorem ay_mwca_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMWCACheckerReplay checkerAccepted replayTrace -> checkerAccepted :=
  fun h => ay_mwca_conj_left h

theorem ay_mwca_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMWCACheckerReplay checkerAccepted replayTrace -> replayTrace :=
  fun h => ay_mwca_conj_right h

theorem ay_mwca_solver_build_intro
    {buildId witnessBuild buildAgreement : Prop} :
    buildId ->
    witnessBuild ->
    buildAgreement ->
    AyMWCASolverBuild buildId witnessBuild buildAgreement :=
  fun hbuild hwitness hagree =>
    ay_mwca_conj_intro hbuild
      (ay_mwca_conj_intro hwitness hagree)

theorem ay_mwca_solver_build_id
    {buildId witnessBuild buildAgreement : Prop} :
    AyMWCASolverBuild buildId witnessBuild buildAgreement -> buildId :=
  fun h => ay_mwca_conj_left h

theorem ay_mwca_solver_build_witness
    {buildId witnessBuild buildAgreement : Prop} :
    AyMWCASolverBuild buildId witnessBuild buildAgreement -> witnessBuild :=
  fun h => ay_mwca_conj_left (ay_mwca_conj_right h)

theorem ay_mwca_solver_build_agreement
    {buildId witnessBuild buildAgreement : Prop} :
    AyMWCASolverBuild buildId witnessBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_mwca_conj_right (ay_mwca_conj_right h)

theorem ay_mwca_original_fingerprint_intro
    {originalFingerprint witnessFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    witnessFingerprint ->
    fingerprintAgreement ->
    AyMWCAOriginalFingerprint
      originalFingerprint witnessFingerprint fingerprintAgreement :=
  fun horiginal hwitness hagree =>
    ay_mwca_conj_intro horiginal
      (ay_mwca_conj_intro hwitness hagree)

theorem ay_mwca_original_fingerprint_original
    {originalFingerprint witnessFingerprint fingerprintAgreement : Prop} :
    AyMWCAOriginalFingerprint
      originalFingerprint witnessFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_mwca_conj_left h

theorem ay_mwca_original_fingerprint_witness
    {originalFingerprint witnessFingerprint fingerprintAgreement : Prop} :
    AyMWCAOriginalFingerprint
      originalFingerprint witnessFingerprint fingerprintAgreement ->
    witnessFingerprint :=
  fun h => ay_mwca_conj_left (ay_mwca_conj_right h)

theorem ay_mwca_original_fingerprint_agreement
    {originalFingerprint witnessFingerprint fingerprintAgreement : Prop} :
    AyMWCAOriginalFingerprint
      originalFingerprint witnessFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mwca_conj_right (ay_mwca_conj_right h)

theorem ay_mwca_canonicalization_evidence_intro
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk : Prop} :
    orderOk ->
    digestOk ->
    reconstructionOk ->
    mapOk ->
    replayOk ->
    buildOk ->
    fingerprintOk ->
    AyMWCACanonicalizationEvidence
      orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk :=
  fun horder hdigest hreconstruction hmap hreplay hbuild hfingerprint =>
    ay_mwca_conj_intro horder
      (ay_mwca_conj_intro hdigest
        (ay_mwca_conj_intro hreconstruction
          (ay_mwca_conj_intro hmap
            (ay_mwca_conj_intro hreplay
              (ay_mwca_conj_intro hbuild hfingerprint)))))

theorem ay_mwca_canonicalization_evidence_order
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWCACanonicalizationEvidence
      orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk ->
    orderOk :=
  fun h => ay_mwca_conj_left h

theorem ay_mwca_canonicalization_evidence_digest
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWCACanonicalizationEvidence
      orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_mwca_conj_left (ay_mwca_conj_right h)

theorem ay_mwca_canonicalization_evidence_reconstruction
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWCACanonicalizationEvidence
      orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk ->
    reconstructionOk :=
  fun h => ay_mwca_conj_left
    (ay_mwca_conj_right (ay_mwca_conj_right h))

theorem ay_mwca_canonicalization_evidence_map
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWCACanonicalizationEvidence
      orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk ->
    mapOk :=
  fun h => ay_mwca_conj_left
    (ay_mwca_conj_right
      (ay_mwca_conj_right (ay_mwca_conj_right h)))

theorem ay_mwca_canonicalization_evidence_replay
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWCACanonicalizationEvidence
      orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk ->
    replayOk :=
  fun h => ay_mwca_conj_left
    (ay_mwca_conj_right
      (ay_mwca_conj_right
        (ay_mwca_conj_right (ay_mwca_conj_right h))))

theorem ay_mwca_canonicalization_evidence_build
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWCACanonicalizationEvidence
      orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk ->
    buildOk :=
  fun h => ay_mwca_conj_left
    (ay_mwca_conj_right
      (ay_mwca_conj_right
        (ay_mwca_conj_right
          (ay_mwca_conj_right (ay_mwca_conj_right h)))))

theorem ay_mwca_canonicalization_evidence_fingerprint
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMWCACanonicalizationEvidence
      orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk ->
    fingerprintOk :=
  fun h => ay_mwca_conj_right
    (ay_mwca_conj_right
      (ay_mwca_conj_right
        (ay_mwca_conj_right
          (ay_mwca_conj_right (ay_mwca_conj_right h)))))

theorem ay_mwca_public_sat_result_intro
    {canonicalEvidence canonicalWitness publicSatClaim : Prop} :
    canonicalEvidence ->
    canonicalWitness ->
    publicSatClaim ->
    AyMWCAPublicSatResult
      canonicalEvidence canonicalWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mwca_conj_intro hevidence
      (ay_mwca_conj_intro hwitness hclaim)

theorem ay_mwca_public_sat_result_evidence
    {canonicalEvidence canonicalWitness publicSatClaim : Prop} :
    AyMWCAPublicSatResult
      canonicalEvidence canonicalWitness publicSatClaim ->
    canonicalEvidence :=
  fun h => ay_mwca_conj_left h

theorem ay_mwca_public_sat_result_witness
    {canonicalEvidence canonicalWitness publicSatClaim : Prop} :
    AyMWCAPublicSatResult
      canonicalEvidence canonicalWitness publicSatClaim ->
    canonicalWitness :=
  fun h => ay_mwca_conj_left (ay_mwca_conj_right h)

theorem ay_mwca_public_sat_result_claim
    {canonicalEvidence canonicalWitness publicSatClaim : Prop} :
    AyMWCAPublicSatResult
      canonicalEvidence canonicalWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mwca_conj_right (ay_mwca_conj_right h)

theorem ay_mwca_accepted_canonicalization_validates_same_public_sat
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk fingerprintOk
      sourcePublicSat canonicalWitness publicSatClaim : Prop} :
    AyMWCACanonicalizationEvidence
      orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk ->
    sourcePublicSat ->
    canonicalWitness ->
    (sourcePublicSat -> publicSatClaim) ->
    AyMWCAPublicSatResult
      (AyMWCACanonicalizationEvidence
        orderOk digestOk reconstructionOk mapOk replayOk buildOk
        fingerprintOk)
      canonicalWitness
      publicSatClaim :=
  fun hevidence hsource hwitness lift =>
    ay_mwca_public_sat_result_intro hevidence hwitness (lift hsource)

theorem ay_mwca_canonicalization_preserves_public_claim
    {sourceWitness canonicalWitness publicSatClaim : Prop} :
    AyMWCAEquisat sourceWitness canonicalWitness ->
    sourceWitness ->
    (canonicalWitness -> publicSatClaim) ->
    publicSatClaim :=
  fun heq hsource publish =>
    publish (ay_mwca_equisat_forward heq hsource)

theorem ay_mwca_publication_requires_order
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk canonicalWitness publicSatClaim : Prop} :
    AyMWCAPublicSatResult
      (AyMWCACanonicalizationEvidence
        orderOk digestOk reconstructionOk mapOk replayOk buildOk
        fingerprintOk)
      canonicalWitness
      publicSatClaim ->
    orderOk :=
  fun h =>
    ay_mwca_canonicalization_evidence_order
      (ay_mwca_public_sat_result_evidence h)

theorem ay_mwca_publication_requires_digest
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk canonicalWitness publicSatClaim : Prop} :
    AyMWCAPublicSatResult
      (AyMWCACanonicalizationEvidence
        orderOk digestOk reconstructionOk mapOk replayOk buildOk
        fingerprintOk)
      canonicalWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mwca_canonicalization_evidence_digest
      (ay_mwca_public_sat_result_evidence h)

theorem ay_mwca_publication_requires_reconstruction
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk canonicalWitness publicSatClaim : Prop} :
    AyMWCAPublicSatResult
      (AyMWCACanonicalizationEvidence
        orderOk digestOk reconstructionOk mapOk replayOk buildOk
        fingerprintOk)
      canonicalWitness
      publicSatClaim ->
    reconstructionOk :=
  fun h =>
    ay_mwca_canonicalization_evidence_reconstruction
      (ay_mwca_public_sat_result_evidence h)

theorem ay_mwca_publication_requires_map
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk canonicalWitness publicSatClaim : Prop} :
    AyMWCAPublicSatResult
      (AyMWCACanonicalizationEvidence
        orderOk digestOk reconstructionOk mapOk replayOk buildOk
        fingerprintOk)
      canonicalWitness
      publicSatClaim ->
    mapOk :=
  fun h =>
    ay_mwca_canonicalization_evidence_map
      (ay_mwca_public_sat_result_evidence h)

theorem ay_mwca_publication_requires_replay
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk canonicalWitness publicSatClaim : Prop} :
    AyMWCAPublicSatResult
      (AyMWCACanonicalizationEvidence
        orderOk digestOk reconstructionOk mapOk replayOk buildOk
        fingerprintOk)
      canonicalWitness
      publicSatClaim ->
    replayOk :=
  fun h =>
    ay_mwca_canonicalization_evidence_replay
      (ay_mwca_public_sat_result_evidence h)

theorem ay_mwca_publication_requires_build
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk canonicalWitness publicSatClaim : Prop} :
    AyMWCAPublicSatResult
      (AyMWCACanonicalizationEvidence
        orderOk digestOk reconstructionOk mapOk replayOk buildOk
        fingerprintOk)
      canonicalWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mwca_canonicalization_evidence_build
      (ay_mwca_public_sat_result_evidence h)

theorem ay_mwca_publication_requires_fingerprint
    {orderOk digestOk reconstructionOk mapOk replayOk buildOk
      fingerprintOk canonicalWitness publicSatClaim : Prop} :
    AyMWCAPublicSatResult
      (AyMWCACanonicalizationEvidence
        orderOk digestOk reconstructionOk mapOk replayOk buildOk
        fingerprintOk)
      canonicalWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mwca_canonicalization_evidence_fingerprint
      (ay_mwca_public_sat_result_evidence h)

theorem ay_mwca_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMWCANoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_mwca_conj_intro hdiagnostic hblocks

theorem ay_mwca_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMWCANoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_mwca_conj_left h

theorem ay_mwca_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMWCANoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_mwca_conj_right h

theorem ay_mwca_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMWCARecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_mwca_conj_intro hreason hrecompute

theorem ay_mwca_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMWCARecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_mwca_conj_left h

theorem ay_mwca_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMWCARecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_mwca_conj_right h

theorem ay_mwca_duplicate_assignments_no_claim
    {duplicateAssignments publicSatClaim : Prop} :
    duplicateAssignments ->
    (publicSatClaim -> False) ->
    AyMWCANoClaimDiagnostic duplicateAssignments publicSatClaim :=
  fun hdup hblocks => ay_mwca_no_claim_diagnostic_intro hdup hblocks

theorem ay_mwca_missing_variables_recompute
    {missingVariables recomputeRequest : Prop} :
    missingVariables ->
    recomputeRequest ->
    AyMWCARecomputeObligation missingVariables recomputeRequest :=
  fun hmissing hrecompute =>
    ay_mwca_recompute_obligation_intro hmissing hrecompute

theorem ay_mwca_missing_variables_no_claim
    {missingVariables publicSatClaim : Prop} :
    missingVariables ->
    (publicSatClaim -> False) ->
    AyMWCANoClaimDiagnostic missingVariables publicSatClaim :=
  fun hmissing hblocks =>
    ay_mwca_no_claim_diagnostic_intro hmissing hblocks

theorem ay_mwca_order_drift_no_claim
    {orderDrift publicSatClaim : Prop} :
    orderDrift ->
    (publicSatClaim -> False) ->
    AyMWCANoClaimDiagnostic orderDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwca_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwca_map_drift_no_claim
    {mapDrift publicSatClaim : Prop} :
    mapDrift ->
    (publicSatClaim -> False) ->
    AyMWCANoClaimDiagnostic mapDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwca_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwca_digest_mismatch_no_claim
    {digestMismatch publicSatClaim : Prop} :
    digestMismatch ->
    (publicSatClaim -> False) ->
    AyMWCANoClaimDiagnostic digestMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_mwca_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_mwca_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMWCANoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks => ay_mwca_no_claim_diagnostic_intro hreject hblocks

theorem ay_mwca_stale_build_no_claim
    {staleBuild publicSatClaim : Prop} :
    staleBuild ->
    (publicSatClaim -> False) ->
    AyMWCANoClaimDiagnostic staleBuild publicSatClaim :=
  fun hstale hblocks => ay_mwca_no_claim_diagnostic_intro hstale hblocks

theorem ay_mwca_fingerprint_drift_no_claim
    {fingerprintDrift publicSatClaim : Prop} :
    fingerprintDrift ->
    (publicSatClaim -> False) ->
    AyMWCANoClaimDiagnostic fingerprintDrift publicSatClaim :=
  fun hdrift hblocks => ay_mwca_no_claim_diagnostic_intro hdrift hblocks

theorem ay_mwca_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMWCANoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mwca_no_claim_diagnostic_blocks h hclaim

theorem ay_mwca_bad_canonicalization_cannot_publish_sat
    {badCanonicalization publicSatClaim : Prop} :
    AyMWCANoClaimDiagnostic badCanonicalization publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_mwca_diagnostic_blocks_public_claim h hclaim
