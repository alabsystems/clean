-- SAT-COMP/ay assignment order-independence soundness skeleton.
-- Public SAT emission may ignore solver-trail assignment order only when a
-- canonical DIMACS projection, replayable digest, checker replay, build, and
-- original fingerprint evidence agree.

def AyMAOIConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMAOIDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMAOIEquisat (left right : Prop) : Prop :=
  AyMAOIConj (left -> right) (right -> left)

def AyMAOIOrderIndependentCheck
    (trailCheck canonicalCheck orderInvariant : Prop) : Prop :=
  AyMAOIConj trailCheck (AyMAOIConj canonicalCheck orderInvariant)

def AyMAOICanonicalProjection
    (solverTrailOrder publicDimacsOrder projectionAgreement : Prop) : Prop :=
  AyMAOIConj solverTrailOrder
    (AyMAOIConj publicDimacsOrder projectionAgreement)

def AyMAOIDuplicateNoiseTolerance
    (duplicateOrNoise replayableDigest equivalentAssignments : Prop) : Prop :=
  AyMAOIConj duplicateOrNoise
    (AyMAOIConj replayableDigest equivalentAssignments)

def AyMAOIAssignmentDigest
    (trailDigest canonicalDigest digestAgreement : Prop) : Prop :=
  AyMAOIConj trailDigest (AyMAOIConj canonicalDigest digestAgreement)

def AyMAOICheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMAOIConj checkerAccepted replayTrace

def AyMAOISolverBuild
    (solverBuild witnessBuild buildAgreement : Prop) : Prop :=
  AyMAOIConj solverBuild (AyMAOIConj witnessBuild buildAgreement)

def AyMAOIOriginalFingerprint
    (originalFingerprint witnessFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMAOIConj originalFingerprint
    (AyMAOIConj witnessFingerprint fingerprintAgreement)

def AyMAOIEmissionEvidence
    (orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk : Prop) : Prop :=
  AyMAOIConj orderOk
    (AyMAOIConj projectionOk
      (AyMAOIConj duplicateOk
        (AyMAOIConj digestOk
          (AyMAOIConj replayOk
            (AyMAOIConj buildOk fingerprintOk)))))

def AyMAOIPublicSatResult
    (emissionEvidence publicWitness publicSatClaim : Prop) : Prop :=
  AyMAOIConj emissionEvidence
    (AyMAOIConj publicWitness publicSatClaim)

def AyMAOINoClaimDiagnostic (diagnostic publicSatClaim : Prop) : Prop :=
  AyMAOIConj diagnostic (publicSatClaim -> False)

def AyMAOIRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMAOIConj reason recomputeRequest

theorem ay_maoi_conj_intro {left right : Prop} :
    left -> right -> AyMAOIConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_maoi_conj_left {left right : Prop} :
    AyMAOIConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_maoi_conj_right {left right : Prop} :
    AyMAOIConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_maoi_disj_left {left right : Prop} :
    left -> AyMAOIDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_maoi_disj_right {left right : Prop} :
    right -> AyMAOIDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_maoi_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMAOIEquisat left right :=
  fun hf hb => ay_maoi_conj_intro hf hb

theorem ay_maoi_equisat_forward {left right : Prop} :
    AyMAOIEquisat left right -> left -> right :=
  fun h => ay_maoi_conj_left h

theorem ay_maoi_equisat_backward {left right : Prop} :
    AyMAOIEquisat left right -> right -> left :=
  fun h => ay_maoi_conj_right h

theorem ay_maoi_order_independent_check_intro
    {trailCheck canonicalCheck orderInvariant : Prop} :
    trailCheck ->
    canonicalCheck ->
    orderInvariant ->
    AyMAOIOrderIndependentCheck trailCheck canonicalCheck orderInvariant :=
  fun htrail hcanonical hinvariant =>
    ay_maoi_conj_intro htrail
      (ay_maoi_conj_intro hcanonical hinvariant)

theorem ay_maoi_order_independent_check_trail
    {trailCheck canonicalCheck orderInvariant : Prop} :
    AyMAOIOrderIndependentCheck trailCheck canonicalCheck orderInvariant ->
    trailCheck :=
  fun h => ay_maoi_conj_left h

theorem ay_maoi_order_independent_check_canonical
    {trailCheck canonicalCheck orderInvariant : Prop} :
    AyMAOIOrderIndependentCheck trailCheck canonicalCheck orderInvariant ->
    canonicalCheck :=
  fun h => ay_maoi_conj_left (ay_maoi_conj_right h)

theorem ay_maoi_order_independent_check_invariant
    {trailCheck canonicalCheck orderInvariant : Prop} :
    AyMAOIOrderIndependentCheck trailCheck canonicalCheck orderInvariant ->
    orderInvariant :=
  fun h => ay_maoi_conj_right (ay_maoi_conj_right h)

theorem ay_maoi_canonical_projection_intro
    {solverTrailOrder publicDimacsOrder projectionAgreement : Prop} :
    solverTrailOrder ->
    publicDimacsOrder ->
    projectionAgreement ->
    AyMAOICanonicalProjection
      solverTrailOrder publicDimacsOrder projectionAgreement :=
  fun hsolver hpublic hagree =>
    ay_maoi_conj_intro hsolver
      (ay_maoi_conj_intro hpublic hagree)

theorem ay_maoi_canonical_projection_solver
    {solverTrailOrder publicDimacsOrder projectionAgreement : Prop} :
    AyMAOICanonicalProjection
      solverTrailOrder publicDimacsOrder projectionAgreement ->
    solverTrailOrder :=
  fun h => ay_maoi_conj_left h

theorem ay_maoi_canonical_projection_public
    {solverTrailOrder publicDimacsOrder projectionAgreement : Prop} :
    AyMAOICanonicalProjection
      solverTrailOrder publicDimacsOrder projectionAgreement ->
    publicDimacsOrder :=
  fun h => ay_maoi_conj_left (ay_maoi_conj_right h)

theorem ay_maoi_canonical_projection_agreement
    {solverTrailOrder publicDimacsOrder projectionAgreement : Prop} :
    AyMAOICanonicalProjection
      solverTrailOrder publicDimacsOrder projectionAgreement ->
    projectionAgreement :=
  fun h => ay_maoi_conj_right (ay_maoi_conj_right h)

theorem ay_maoi_duplicate_noise_tolerance_intro
    {duplicateOrNoise replayableDigest equivalentAssignments : Prop} :
    duplicateOrNoise ->
    replayableDigest ->
    equivalentAssignments ->
    AyMAOIDuplicateNoiseTolerance
      duplicateOrNoise replayableDigest equivalentAssignments :=
  fun hnoise hdigest hequiv =>
    ay_maoi_conj_intro hnoise
      (ay_maoi_conj_intro hdigest hequiv)

theorem ay_maoi_duplicate_noise_tolerance_noise
    {duplicateOrNoise replayableDigest equivalentAssignments : Prop} :
    AyMAOIDuplicateNoiseTolerance
      duplicateOrNoise replayableDigest equivalentAssignments ->
    duplicateOrNoise :=
  fun h => ay_maoi_conj_left h

theorem ay_maoi_duplicate_noise_tolerance_digest
    {duplicateOrNoise replayableDigest equivalentAssignments : Prop} :
    AyMAOIDuplicateNoiseTolerance
      duplicateOrNoise replayableDigest equivalentAssignments ->
    replayableDigest :=
  fun h => ay_maoi_conj_left (ay_maoi_conj_right h)

theorem ay_maoi_duplicate_noise_tolerance_equivalent
    {duplicateOrNoise replayableDigest equivalentAssignments : Prop} :
    AyMAOIDuplicateNoiseTolerance
      duplicateOrNoise replayableDigest equivalentAssignments ->
    equivalentAssignments :=
  fun h => ay_maoi_conj_right (ay_maoi_conj_right h)

theorem ay_maoi_assignment_digest_intro
    {trailDigest canonicalDigest digestAgreement : Prop} :
    trailDigest ->
    canonicalDigest ->
    digestAgreement ->
    AyMAOIAssignmentDigest trailDigest canonicalDigest digestAgreement :=
  fun htrail hcanonical hagree =>
    ay_maoi_conj_intro htrail
      (ay_maoi_conj_intro hcanonical hagree)

theorem ay_maoi_assignment_digest_trail
    {trailDigest canonicalDigest digestAgreement : Prop} :
    AyMAOIAssignmentDigest trailDigest canonicalDigest digestAgreement ->
    trailDigest :=
  fun h => ay_maoi_conj_left h

theorem ay_maoi_assignment_digest_canonical
    {trailDigest canonicalDigest digestAgreement : Prop} :
    AyMAOIAssignmentDigest trailDigest canonicalDigest digestAgreement ->
    canonicalDigest :=
  fun h => ay_maoi_conj_left (ay_maoi_conj_right h)

theorem ay_maoi_assignment_digest_agreement
    {trailDigest canonicalDigest digestAgreement : Prop} :
    AyMAOIAssignmentDigest trailDigest canonicalDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_maoi_conj_right (ay_maoi_conj_right h)

theorem ay_maoi_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMAOICheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_maoi_conj_intro haccepted htrace

theorem ay_maoi_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMAOICheckerReplay checkerAccepted replayTrace -> checkerAccepted :=
  fun h => ay_maoi_conj_left h

theorem ay_maoi_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMAOICheckerReplay checkerAccepted replayTrace -> replayTrace :=
  fun h => ay_maoi_conj_right h

theorem ay_maoi_solver_build_intro
    {solverBuild witnessBuild buildAgreement : Prop} :
    solverBuild ->
    witnessBuild ->
    buildAgreement ->
    AyMAOISolverBuild solverBuild witnessBuild buildAgreement :=
  fun hsolver hwitness hagree =>
    ay_maoi_conj_intro hsolver
      (ay_maoi_conj_intro hwitness hagree)

theorem ay_maoi_solver_build_solver
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMAOISolverBuild solverBuild witnessBuild buildAgreement ->
    solverBuild :=
  fun h => ay_maoi_conj_left h

theorem ay_maoi_solver_build_witness
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMAOISolverBuild solverBuild witnessBuild buildAgreement ->
    witnessBuild :=
  fun h => ay_maoi_conj_left (ay_maoi_conj_right h)

theorem ay_maoi_solver_build_agreement
    {solverBuild witnessBuild buildAgreement : Prop} :
    AyMAOISolverBuild solverBuild witnessBuild buildAgreement ->
    buildAgreement :=
  fun h => ay_maoi_conj_right (ay_maoi_conj_right h)

theorem ay_maoi_original_fingerprint_intro
    {originalFingerprint witnessFingerprint fingerprintAgreement : Prop} :
    originalFingerprint ->
    witnessFingerprint ->
    fingerprintAgreement ->
    AyMAOIOriginalFingerprint
      originalFingerprint witnessFingerprint fingerprintAgreement :=
  fun horiginal hwitness hagree =>
    ay_maoi_conj_intro horiginal
      (ay_maoi_conj_intro hwitness hagree)

theorem ay_maoi_original_fingerprint_original
    {originalFingerprint witnessFingerprint fingerprintAgreement : Prop} :
    AyMAOIOriginalFingerprint
      originalFingerprint witnessFingerprint fingerprintAgreement ->
    originalFingerprint :=
  fun h => ay_maoi_conj_left h

theorem ay_maoi_original_fingerprint_witness
    {originalFingerprint witnessFingerprint fingerprintAgreement : Prop} :
    AyMAOIOriginalFingerprint
      originalFingerprint witnessFingerprint fingerprintAgreement ->
    witnessFingerprint :=
  fun h => ay_maoi_conj_left (ay_maoi_conj_right h)

theorem ay_maoi_original_fingerprint_agreement
    {originalFingerprint witnessFingerprint fingerprintAgreement : Prop} :
    AyMAOIOriginalFingerprint
      originalFingerprint witnessFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_maoi_conj_right (ay_maoi_conj_right h)

theorem ay_maoi_emission_evidence_intro
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    orderOk ->
    projectionOk ->
    duplicateOk ->
    digestOk ->
    replayOk ->
    buildOk ->
    fingerprintOk ->
    AyMAOIEmissionEvidence
      orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk :=
  fun horder hprojection hduplicate hdigest hreplay hbuild hfingerprint =>
    ay_maoi_conj_intro horder
      (ay_maoi_conj_intro hprojection
        (ay_maoi_conj_intro hduplicate
          (ay_maoi_conj_intro hdigest
            (ay_maoi_conj_intro hreplay
              (ay_maoi_conj_intro hbuild hfingerprint)))))

theorem ay_maoi_emission_evidence_order
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMAOIEmissionEvidence
      orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk ->
    orderOk :=
  fun h => ay_maoi_conj_left h

theorem ay_maoi_emission_evidence_projection
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMAOIEmissionEvidence
      orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk ->
    projectionOk :=
  fun h => ay_maoi_conj_left (ay_maoi_conj_right h)

theorem ay_maoi_emission_evidence_duplicate
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMAOIEmissionEvidence
      orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk ->
    duplicateOk :=
  fun h => ay_maoi_conj_left
    (ay_maoi_conj_right (ay_maoi_conj_right h))

theorem ay_maoi_emission_evidence_digest
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMAOIEmissionEvidence
      orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_maoi_conj_left
    (ay_maoi_conj_right
      (ay_maoi_conj_right (ay_maoi_conj_right h)))

theorem ay_maoi_emission_evidence_replay
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMAOIEmissionEvidence
      orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk ->
    replayOk :=
  fun h => ay_maoi_conj_left
    (ay_maoi_conj_right
      (ay_maoi_conj_right
        (ay_maoi_conj_right (ay_maoi_conj_right h))))

theorem ay_maoi_emission_evidence_build
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMAOIEmissionEvidence
      orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk ->
    buildOk :=
  fun h => ay_maoi_conj_left
    (ay_maoi_conj_right
      (ay_maoi_conj_right
        (ay_maoi_conj_right
          (ay_maoi_conj_right (ay_maoi_conj_right h)))))

theorem ay_maoi_emission_evidence_fingerprint
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk : Prop} :
    AyMAOIEmissionEvidence
      orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk ->
    fingerprintOk :=
  fun h => ay_maoi_conj_right
    (ay_maoi_conj_right
      (ay_maoi_conj_right
        (ay_maoi_conj_right
          (ay_maoi_conj_right (ay_maoi_conj_right h)))))

theorem ay_maoi_public_sat_result_intro
    {emissionEvidence publicWitness publicSatClaim : Prop} :
    emissionEvidence ->
    publicWitness ->
    publicSatClaim ->
    AyMAOIPublicSatResult
      emissionEvidence publicWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_maoi_conj_intro hevidence
      (ay_maoi_conj_intro hwitness hclaim)

theorem ay_maoi_public_sat_result_evidence
    {emissionEvidence publicWitness publicSatClaim : Prop} :
    AyMAOIPublicSatResult
      emissionEvidence publicWitness publicSatClaim ->
    emissionEvidence :=
  fun h => ay_maoi_conj_left h

theorem ay_maoi_public_sat_result_witness
    {emissionEvidence publicWitness publicSatClaim : Prop} :
    AyMAOIPublicSatResult
      emissionEvidence publicWitness publicSatClaim ->
    publicWitness :=
  fun h => ay_maoi_conj_left (ay_maoi_conj_right h)

theorem ay_maoi_public_sat_result_claim
    {emissionEvidence publicWitness publicSatClaim : Prop} :
    AyMAOIPublicSatResult
      emissionEvidence publicWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_maoi_conj_right (ay_maoi_conj_right h)

theorem ay_maoi_accepted_evidence_emits_public_sat
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk fingerprintOk
      publicWitness publicSatClaim : Prop} :
    AyMAOIEmissionEvidence
      orderOk projectionOk duplicateOk digestOk replayOk buildOk
      fingerprintOk ->
    publicWitness ->
    publicSatClaim ->
    AyMAOIPublicSatResult
      (AyMAOIEmissionEvidence
        orderOk projectionOk duplicateOk digestOk replayOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_maoi_public_sat_result_intro hevidence hwitness hclaim

theorem ay_maoi_public_sat_requires_accepted_evidence
    {emissionEvidence publicWitness publicSatClaim : Prop} :
    AyMAOIPublicSatResult emissionEvidence publicWitness publicSatClaim ->
    emissionEvidence :=
  fun h => ay_maoi_public_sat_result_evidence h

theorem ay_maoi_admissible_ordering_hints_preserve_truth
    {trailTruth publicTruth : Prop} :
    AyMAOIEquisat trailTruth publicTruth ->
    trailTruth ->
    publicTruth :=
  fun heq htrail => ay_maoi_equisat_forward heq htrail

theorem ay_maoi_duplicate_noise_preserves_truth_with_digest
    {duplicateOrNoise replayableDigest equivalentAssignments publicTruth :
      Prop} :
    AyMAOIDuplicateNoiseTolerance
      duplicateOrNoise replayableDigest equivalentAssignments ->
    (replayableDigest -> equivalentAssignments -> publicTruth) ->
    publicTruth :=
  fun h publish =>
    publish
      (ay_maoi_duplicate_noise_tolerance_digest h)
      (ay_maoi_duplicate_noise_tolerance_equivalent h)

theorem ay_maoi_publication_requires_order
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk fingerprintOk
      publicWitness publicSatClaim : Prop} :
    AyMAOIPublicSatResult
      (AyMAOIEmissionEvidence
        orderOk projectionOk duplicateOk digestOk replayOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    orderOk :=
  fun h =>
    ay_maoi_emission_evidence_order
      (ay_maoi_public_sat_result_evidence h)

theorem ay_maoi_publication_requires_projection
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk fingerprintOk
      publicWitness publicSatClaim : Prop} :
    AyMAOIPublicSatResult
      (AyMAOIEmissionEvidence
        orderOk projectionOk duplicateOk digestOk replayOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    projectionOk :=
  fun h =>
    ay_maoi_emission_evidence_projection
      (ay_maoi_public_sat_result_evidence h)

theorem ay_maoi_publication_requires_duplicate_policy
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk fingerprintOk
      publicWitness publicSatClaim : Prop} :
    AyMAOIPublicSatResult
      (AyMAOIEmissionEvidence
        orderOk projectionOk duplicateOk digestOk replayOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    duplicateOk :=
  fun h =>
    ay_maoi_emission_evidence_duplicate
      (ay_maoi_public_sat_result_evidence h)

theorem ay_maoi_publication_requires_digest
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk fingerprintOk
      publicWitness publicSatClaim : Prop} :
    AyMAOIPublicSatResult
      (AyMAOIEmissionEvidence
        orderOk projectionOk duplicateOk digestOk replayOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    digestOk :=
  fun h =>
    ay_maoi_emission_evidence_digest
      (ay_maoi_public_sat_result_evidence h)

theorem ay_maoi_publication_requires_replay
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk fingerprintOk
      publicWitness publicSatClaim : Prop} :
    AyMAOIPublicSatResult
      (AyMAOIEmissionEvidence
        orderOk projectionOk duplicateOk digestOk replayOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    replayOk :=
  fun h =>
    ay_maoi_emission_evidence_replay
      (ay_maoi_public_sat_result_evidence h)

theorem ay_maoi_publication_requires_build
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk fingerprintOk
      publicWitness publicSatClaim : Prop} :
    AyMAOIPublicSatResult
      (AyMAOIEmissionEvidence
        orderOk projectionOk duplicateOk digestOk replayOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    buildOk :=
  fun h =>
    ay_maoi_emission_evidence_build
      (ay_maoi_public_sat_result_evidence h)

theorem ay_maoi_publication_requires_fingerprint
    {orderOk projectionOk duplicateOk digestOk replayOk buildOk fingerprintOk
      publicWitness publicSatClaim : Prop} :
    AyMAOIPublicSatResult
      (AyMAOIEmissionEvidence
        orderOk projectionOk duplicateOk digestOk replayOk buildOk
        fingerprintOk)
      publicWitness
      publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_maoi_emission_evidence_fingerprint
      (ay_maoi_public_sat_result_evidence h)

theorem ay_maoi_no_claim_diagnostic_intro
    {diagnostic publicSatClaim : Prop} :
    diagnostic ->
    (publicSatClaim -> False) ->
    AyMAOINoClaimDiagnostic diagnostic publicSatClaim :=
  fun hdiagnostic hblocks =>
    ay_maoi_conj_intro hdiagnostic hblocks

theorem ay_maoi_no_claim_diagnostic_reason
    {diagnostic publicSatClaim : Prop} :
    AyMAOINoClaimDiagnostic diagnostic publicSatClaim -> diagnostic :=
  fun h => ay_maoi_conj_left h

theorem ay_maoi_no_claim_diagnostic_blocks
    {diagnostic publicSatClaim : Prop} :
    AyMAOINoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h => ay_maoi_conj_right h

theorem ay_maoi_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMAOIRecomputeObligation reason recomputeRequest :=
  fun hreason hrecompute => ay_maoi_conj_intro hreason hrecompute

theorem ay_maoi_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMAOIRecomputeObligation reason recomputeRequest -> reason :=
  fun h => ay_maoi_conj_left h

theorem ay_maoi_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMAOIRecomputeObligation reason recomputeRequest -> recomputeRequest :=
  fun h => ay_maoi_conj_right h

theorem ay_maoi_order_drift_no_claim
    {orderDrift publicSatClaim : Prop} :
    orderDrift ->
    (publicSatClaim -> False) ->
    AyMAOINoClaimDiagnostic orderDrift publicSatClaim :=
  fun hdrift hblocks => ay_maoi_no_claim_diagnostic_intro hdrift hblocks

theorem ay_maoi_missing_projection_recompute
    {missingProjection recomputeRequest : Prop} :
    missingProjection ->
    recomputeRequest ->
    AyMAOIRecomputeObligation missingProjection recomputeRequest :=
  fun hmissing hrecompute =>
    ay_maoi_recompute_obligation_intro hmissing hrecompute

theorem ay_maoi_missing_projection_no_claim
    {missingProjection publicSatClaim : Prop} :
    missingProjection ->
    (publicSatClaim -> False) ->
    AyMAOINoClaimDiagnostic missingProjection publicSatClaim :=
  fun hmissing hblocks =>
    ay_maoi_no_claim_diagnostic_intro hmissing hblocks

theorem ay_maoi_duplicate_conflict_no_claim
    {duplicateConflict publicSatClaim : Prop} :
    duplicateConflict ->
    (publicSatClaim -> False) ->
    AyMAOINoClaimDiagnostic duplicateConflict publicSatClaim :=
  fun hconflict hblocks =>
    ay_maoi_no_claim_diagnostic_intro hconflict hblocks

theorem ay_maoi_stale_solver_build_no_claim
    {staleSolverBuild publicSatClaim : Prop} :
    staleSolverBuild ->
    (publicSatClaim -> False) ->
    AyMAOINoClaimDiagnostic staleSolverBuild publicSatClaim :=
  fun hstale hblocks => ay_maoi_no_claim_diagnostic_intro hstale hblocks

theorem ay_maoi_checker_rejection_no_claim
    {checkerRejection publicSatClaim : Prop} :
    checkerRejection ->
    (publicSatClaim -> False) ->
    AyMAOINoClaimDiagnostic checkerRejection publicSatClaim :=
  fun hreject hblocks =>
    ay_maoi_no_claim_diagnostic_intro hreject hblocks

theorem ay_maoi_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicSatClaim : Prop} :
    fingerprintMismatch ->
    (publicSatClaim -> False) ->
    AyMAOINoClaimDiagnostic fingerprintMismatch publicSatClaim :=
  fun hmismatch hblocks =>
    ay_maoi_no_claim_diagnostic_intro hmismatch hblocks

theorem ay_maoi_diagnostic_blocks_public_claim
    {diagnostic publicSatClaim : Prop} :
    AyMAOINoClaimDiagnostic diagnostic publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_maoi_no_claim_diagnostic_blocks h hclaim

theorem ay_maoi_bad_order_evidence_cannot_emit_sat
    {badOrderEvidence publicSatClaim : Prop} :
    AyMAOINoClaimDiagnostic badOrderEvidence publicSatClaim ->
    publicSatClaim ->
    False :=
  fun h hclaim => ay_maoi_diagnostic_blocks_public_claim h hclaim
