/- SAT-COMP/ay sparse assignment projection contract.

This self-contained file models the evidence needed to publish only assigned or
relevant SAT variables while preserving the public SAT-COMP model claim.
-/

def AyMSAPConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMSAPDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMSAPEquisat (source target : Prop) : Prop :=
  AyMSAPConj (source -> target) (target -> source)

def AyMSAPSparseProjectionManifest
    (sparseManifest relevantVariables projectionDomain : Prop) : Prop :=
  AyMSAPConj sparseManifest
    (AyMSAPConj relevantVariables projectionDomain)

def AyMSAPReconstructionEvidence
    (sparseAssignment defaultExtension reconstructedAssignment : Prop) : Prop :=
  AyMSAPConj sparseAssignment
    (AyMSAPConj defaultExtension reconstructedAssignment)

def AyMSAPAssignmentDigest
    (sparseDigest fullDigest digestAgreement : Prop) : Prop :=
  AyMSAPConj sparseDigest (AyMSAPConj fullDigest digestAgreement)

def AyMSAPDimacsMaps
    (projectionMap dimacsMap mapAgreement : Prop) : Prop :=
  AyMSAPConj projectionMap (AyMSAPConj dimacsMap mapAgreement)

def AyMSAPClauseReplay
    (clauseReplay sparseEvaluation replayAgreement : Prop) : Prop :=
  AyMSAPConj clauseReplay (AyMSAPConj sparseEvaluation replayAgreement)

def AyMSAPCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyMSAPConj checkerAccepted (AyMSAPConj transcript transcriptAgreement)

def AyMSAPFormulaFingerprint
    (originalFingerprint sparseFingerprint fingerprintAgreement : Prop) : Prop :=
  AyMSAPConj originalFingerprint
    (AyMSAPConj sparseFingerprint fingerprintAgreement)

def AyMSAPBuildEvidence
    (solverBuild projectionBuild buildAgreement : Prop) : Prop :=
  AyMSAPConj solverBuild (AyMSAPConj projectionBuild buildAgreement)

def AyMSAPAcceptedProjection
    (manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop) : Prop :=
  AyMSAPConj manifestOk
    (AyMSAPConj reconstructionOk
      (AyMSAPConj digestOk
        (AyMSAPConj mapsOk
          (AyMSAPConj clauseReplayOk
            (AyMSAPConj checkerOk
              (AyMSAPConj fingerprintOk buildOk))))))

def AyMSAPPublicSatWitness
    (acceptedProjection sparseWitness publicSatClaim : Prop) : Prop :=
  AyMSAPConj acceptedProjection (AyMSAPConj sparseWitness publicSatClaim)

def AyMSAPNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyMSAPConj reason blocksPublication

def AyMSAPRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyMSAPConj reason recomputeRequested

theorem ay_msap_conj_intro {left right : Prop} :
    left -> right -> AyMSAPConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_msap_conj_left {left right : Prop} :
    AyMSAPConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_msap_conj_right {left right : Prop} :
    AyMSAPConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_msap_disj_left {left right : Prop} :
    left -> AyMSAPDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_msap_disj_right {left right : Prop} :
    right -> AyMSAPDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_msap_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyMSAPEquisat source target :=
  fun forward backward => ay_msap_conj_intro forward backward

theorem ay_msap_equisat_forward {source target : Prop} :
    AyMSAPEquisat source target -> source -> target :=
  fun h => ay_msap_conj_left h

theorem ay_msap_equisat_backward {source target : Prop} :
    AyMSAPEquisat source target -> target -> source :=
  fun h => ay_msap_conj_right h

theorem ay_msap_sparse_projection_manifest_intro
    {sparseManifest relevantVariables projectionDomain : Prop} :
    sparseManifest -> relevantVariables -> projectionDomain ->
    AyMSAPSparseProjectionManifest
      sparseManifest relevantVariables projectionDomain :=
  fun hmanifest hrelevant hdomain =>
    ay_msap_conj_intro hmanifest (ay_msap_conj_intro hrelevant hdomain)

theorem ay_msap_sparse_projection_manifest_sparse
    {sparseManifest relevantVariables projectionDomain : Prop} :
    AyMSAPSparseProjectionManifest
      sparseManifest relevantVariables projectionDomain ->
    sparseManifest :=
  fun h => ay_msap_conj_left h

theorem ay_msap_sparse_projection_manifest_relevant
    {sparseManifest relevantVariables projectionDomain : Prop} :
    AyMSAPSparseProjectionManifest
      sparseManifest relevantVariables projectionDomain ->
    relevantVariables :=
  fun h => ay_msap_conj_left (ay_msap_conj_right h)

theorem ay_msap_sparse_projection_manifest_domain
    {sparseManifest relevantVariables projectionDomain : Prop} :
    AyMSAPSparseProjectionManifest
      sparseManifest relevantVariables projectionDomain ->
    projectionDomain :=
  fun h => ay_msap_conj_right (ay_msap_conj_right h)

theorem ay_msap_reconstruction_evidence_intro
    {sparseAssignment defaultExtension reconstructedAssignment : Prop} :
    sparseAssignment -> defaultExtension -> reconstructedAssignment ->
    AyMSAPReconstructionEvidence
      sparseAssignment defaultExtension reconstructedAssignment :=
  fun hsparse hdefault hreconstructed =>
    ay_msap_conj_intro hsparse
      (ay_msap_conj_intro hdefault hreconstructed)

theorem ay_msap_assignment_digest_intro
    {sparseDigest fullDigest digestAgreement : Prop} :
    sparseDigest -> fullDigest -> digestAgreement ->
    AyMSAPAssignmentDigest sparseDigest fullDigest digestAgreement :=
  fun hsparse hfull hagree =>
    ay_msap_conj_intro hsparse (ay_msap_conj_intro hfull hagree)

theorem ay_msap_dimacs_maps_intro
    {projectionMap dimacsMap mapAgreement : Prop} :
    projectionMap -> dimacsMap -> mapAgreement ->
    AyMSAPDimacsMaps projectionMap dimacsMap mapAgreement :=
  fun hprojection hdimacs hagree =>
    ay_msap_conj_intro hprojection (ay_msap_conj_intro hdimacs hagree)

theorem ay_msap_clause_replay_intro
    {clauseReplay sparseEvaluation replayAgreement : Prop} :
    clauseReplay -> sparseEvaluation -> replayAgreement ->
    AyMSAPClauseReplay clauseReplay sparseEvaluation replayAgreement :=
  fun hreplay hevaluation hagree =>
    ay_msap_conj_intro hreplay (ay_msap_conj_intro hevaluation hagree)

theorem ay_msap_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyMSAPCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_msap_conj_intro haccepted (ay_msap_conj_intro htranscript hagree)

theorem ay_msap_formula_fingerprint_intro
    {originalFingerprint sparseFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> sparseFingerprint -> fingerprintAgreement ->
    AyMSAPFormulaFingerprint
      originalFingerprint sparseFingerprint fingerprintAgreement :=
  fun horiginal hsparse hagree =>
    ay_msap_conj_intro horiginal (ay_msap_conj_intro hsparse hagree)

theorem ay_msap_build_evidence_intro
    {solverBuild projectionBuild buildAgreement : Prop} :
    solverBuild -> projectionBuild -> buildAgreement ->
    AyMSAPBuildEvidence solverBuild projectionBuild buildAgreement :=
  fun hsolver hprojection hagree =>
    ay_msap_conj_intro hsolver (ay_msap_conj_intro hprojection hagree)

theorem ay_msap_accepted_projection_intro
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    manifestOk -> reconstructionOk -> digestOk -> mapsOk -> clauseReplayOk ->
    checkerOk -> fingerprintOk -> buildOk ->
    AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
      clauseReplayOk checkerOk fingerprintOk buildOk :=
  fun hmanifest hreconstruction hdigest hmaps hclause hchecker
      hfingerprint hbuild =>
    ay_msap_conj_intro hmanifest
      (ay_msap_conj_intro hreconstruction
        (ay_msap_conj_intro hdigest
          (ay_msap_conj_intro hmaps
            (ay_msap_conj_intro hclause
              (ay_msap_conj_intro hchecker
                (ay_msap_conj_intro hfingerprint hbuild))))))

theorem ay_msap_accepted_projection_manifest
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    manifestOk :=
  fun h => ay_msap_conj_left h

theorem ay_msap_accepted_projection_reconstruction
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    reconstructionOk :=
  fun h => ay_msap_conj_left (ay_msap_conj_right h)

theorem ay_msap_accepted_projection_digest
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    digestOk :=
  fun h => ay_msap_conj_left (ay_msap_conj_right (ay_msap_conj_right h))

theorem ay_msap_accepted_projection_maps
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    mapsOk :=
  fun h =>
    ay_msap_conj_left
      (ay_msap_conj_right (ay_msap_conj_right (ay_msap_conj_right h)))

theorem ay_msap_accepted_projection_clause_replay
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    clauseReplayOk :=
  fun h =>
    ay_msap_conj_left
      (ay_msap_conj_right
        (ay_msap_conj_right (ay_msap_conj_right (ay_msap_conj_right h))))

theorem ay_msap_accepted_projection_checker
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    checkerOk :=
  fun h =>
    ay_msap_conj_left
      (ay_msap_conj_right
        (ay_msap_conj_right
          (ay_msap_conj_right (ay_msap_conj_right (ay_msap_conj_right h)))))

theorem ay_msap_accepted_projection_fingerprint
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    fingerprintOk :=
  fun h =>
    ay_msap_conj_left
      (ay_msap_conj_right
        (ay_msap_conj_right
          (ay_msap_conj_right
            (ay_msap_conj_right (ay_msap_conj_right
              (ay_msap_conj_right h))))))

theorem ay_msap_accepted_projection_build
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    buildOk :=
  fun h =>
    ay_msap_conj_right
      (ay_msap_conj_right
        (ay_msap_conj_right
          (ay_msap_conj_right
            (ay_msap_conj_right (ay_msap_conj_right
              (ay_msap_conj_right h))))))

theorem ay_msap_public_sat_witness_intro
    {acceptedProjection sparseWitness publicSatClaim : Prop} :
    acceptedProjection -> sparseWitness -> publicSatClaim ->
    AyMSAPPublicSatWitness acceptedProjection sparseWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_msap_conj_intro hevidence (ay_msap_conj_intro hwitness hclaim)

theorem ay_msap_public_sat_witness_evidence
    {acceptedProjection sparseWitness publicSatClaim : Prop} :
    AyMSAPPublicSatWitness acceptedProjection sparseWitness publicSatClaim ->
    acceptedProjection :=
  fun h => ay_msap_conj_left h

theorem ay_msap_public_sat_witness_claim
    {acceptedProjection sparseWitness publicSatClaim : Prop} :
    AyMSAPPublicSatWitness acceptedProjection sparseWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_msap_conj_right (ay_msap_conj_right h)

theorem ay_msap_accepted_sparse_projection_publishes_sound_sat
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk sparseWitness publicSatClaim : Prop} :
    AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    sparseWitness -> publicSatClaim ->
    AyMSAPPublicSatWitness
      (AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      sparseWitness publicSatClaim :=
  ay_msap_public_sat_witness_intro

theorem ay_msap_sparse_projection_preserves_truth
    {sparseTruth reconstructedTruth : Prop} :
    AyMSAPEquisat sparseTruth reconstructedTruth ->
    sparseTruth -> reconstructedTruth :=
  ay_msap_equisat_forward

theorem ay_msap_public_sat_requires_accepted_projection
    {acceptedProjection sparseWitness publicSatClaim : Prop} :
    AyMSAPPublicSatWitness acceptedProjection sparseWitness publicSatClaim ->
    acceptedProjection :=
  ay_msap_public_sat_witness_evidence

theorem ay_msap_publication_requires_manifest
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk sparseWitness publicSatClaim : Prop} :
    AyMSAPPublicSatWitness
      (AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      sparseWitness publicSatClaim ->
    manifestOk :=
  fun h =>
    ay_msap_accepted_projection_manifest
      (ay_msap_public_sat_witness_evidence h)

theorem ay_msap_publication_requires_reconstruction
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk sparseWitness publicSatClaim : Prop} :
    AyMSAPPublicSatWitness
      (AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      sparseWitness publicSatClaim ->
    reconstructionOk :=
  fun h =>
    ay_msap_accepted_projection_reconstruction
      (ay_msap_public_sat_witness_evidence h)

theorem ay_msap_publication_requires_digest
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk sparseWitness publicSatClaim : Prop} :
    AyMSAPPublicSatWitness
      (AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      sparseWitness publicSatClaim ->
    digestOk :=
  fun h =>
    ay_msap_accepted_projection_digest
      (ay_msap_public_sat_witness_evidence h)

theorem ay_msap_publication_requires_maps
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk sparseWitness publicSatClaim : Prop} :
    AyMSAPPublicSatWitness
      (AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      sparseWitness publicSatClaim ->
    mapsOk :=
  fun h =>
    ay_msap_accepted_projection_maps
      (ay_msap_public_sat_witness_evidence h)

theorem ay_msap_publication_requires_clause_replay
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk sparseWitness publicSatClaim : Prop} :
    AyMSAPPublicSatWitness
      (AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      sparseWitness publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_msap_accepted_projection_clause_replay
      (ay_msap_public_sat_witness_evidence h)

theorem ay_msap_publication_requires_checker
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk sparseWitness publicSatClaim : Prop} :
    AyMSAPPublicSatWitness
      (AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      sparseWitness publicSatClaim ->
    checkerOk :=
  fun h =>
    ay_msap_accepted_projection_checker
      (ay_msap_public_sat_witness_evidence h)

theorem ay_msap_publication_requires_fingerprint
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk sparseWitness publicSatClaim : Prop} :
    AyMSAPPublicSatWitness
      (AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      sparseWitness publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_msap_accepted_projection_fingerprint
      (ay_msap_public_sat_witness_evidence h)

theorem ay_msap_publication_requires_build
    {manifestOk reconstructionOk digestOk mapsOk clauseReplayOk checkerOk
      fingerprintOk buildOk sparseWitness publicSatClaim : Prop} :
    AyMSAPPublicSatWitness
      (AyMSAPAcceptedProjection manifestOk reconstructionOk digestOk mapsOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      sparseWitness publicSatClaim ->
    buildOk :=
  fun h =>
    ay_msap_accepted_projection_build
      (ay_msap_public_sat_witness_evidence h)

theorem ay_msap_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyMSAPNoClaimDiagnostic reason blocksPublication :=
  ay_msap_conj_intro

theorem ay_msap_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyMSAPNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_msap_conj_right

theorem ay_msap_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyMSAPRecomputeObligation reason recomputeRequested :=
  ay_msap_conj_intro

theorem ay_msap_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyMSAPRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_msap_conj_right

theorem ay_msap_missing_assignment_entry_no_claim
    {missingAssignmentEntry blocksPublication : Prop} :
    missingAssignmentEntry -> blocksPublication ->
    AyMSAPNoClaimDiagnostic missingAssignmentEntry blocksPublication :=
  ay_msap_no_claim_diagnostic_intro

theorem ay_msap_missing_assignment_entry_recompute
    {missingAssignmentEntry recomputeRequested : Prop} :
    missingAssignmentEntry -> recomputeRequested ->
    AyMSAPRecomputeObligation missingAssignmentEntry recomputeRequested :=
  ay_msap_recompute_obligation_intro

theorem ay_msap_projection_mismatch_no_claim
    {projectionMismatch blocksPublication : Prop} :
    projectionMismatch -> blocksPublication ->
    AyMSAPNoClaimDiagnostic projectionMismatch blocksPublication :=
  ay_msap_no_claim_diagnostic_intro

theorem ay_msap_digest_drift_no_claim
    {digestDrift blocksPublication : Prop} :
    digestDrift -> blocksPublication ->
    AyMSAPNoClaimDiagnostic digestDrift blocksPublication :=
  ay_msap_no_claim_diagnostic_intro

theorem ay_msap_stale_fingerprint_no_claim
    {staleFingerprint blocksPublication : Prop} :
    staleFingerprint -> blocksPublication ->
    AyMSAPNoClaimDiagnostic staleFingerprint blocksPublication :=
  ay_msap_no_claim_diagnostic_intro

theorem ay_msap_checker_rejection_no_claim
    {checkerRejected blocksPublication : Prop} :
    checkerRejected -> blocksPublication ->
    AyMSAPNoClaimDiagnostic checkerRejected blocksPublication :=
  ay_msap_no_claim_diagnostic_intro

theorem ay_msap_bad_sparse_projection_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyMSAPNoClaimDiagnostic failure blocksPublication ->
    AyMSAPRecomputeObligation failure recomputeRequested ->
    AyMSAPConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_msap_conj_intro
      (ay_msap_no_claim_diagnostic_blocks hdiagnostic)
      (ay_msap_recompute_obligation_request hrecompute)
