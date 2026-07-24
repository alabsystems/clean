/- SAT-COMP/ay partial-assignment completion contract.

This self-contained package models completing sparse or partial SAT witnesses
back to full DIMACS assignments.  Public SAT output is admissible only when
completion manifests, domain/default evidence, bidirectional maps, replay,
checker, fingerprint, digest, and build evidence all agree.
-/

def AyMPACConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMPACDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMPACEquisat (source target : Prop) : Prop :=
  AyMPACConj (source -> target) (target -> source)

def AyMPACCompletionManifest
    (partialWitness completionPlan completedWitness : Prop) : Prop :=
  AyMPACConj partialWitness (AyMPACConj completionPlan completedWitness)

def AyMPACVariableDomainEvidence
    (originalDomain coveredDomain noMissingVariables : Prop) : Prop :=
  AyMPACConj originalDomain (AyMPACConj coveredDomain noMissingVariables)

def AyMPACDefaultValuePolicy
    (defaultPolicy defaultAssignments policyAgreement : Prop) : Prop :=
  AyMPACConj defaultPolicy (AyMPACConj defaultAssignments policyAgreement)

def AyMPACBidirectionalVariableMaps
    (solverToDimacs dimacsToSolver inverseAgreement : Prop) : Prop :=
  AyMPACConj solverToDimacs (AyMPACConj dimacsToSolver inverseAgreement)

def AyMPACClauseReplay
    (clauseReplay completedEvaluation replayAgreement : Prop) : Prop :=
  AyMPACConj clauseReplay (AyMPACConj completedEvaluation replayAgreement)

def AyMPACCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyMPACConj checkerAccepted (AyMPACConj transcript transcriptAgreement)

def AyMPACFormulaFingerprint
    (originalFingerprint completionFingerprint fingerprintAgreement : Prop) : Prop :=
  AyMPACConj originalFingerprint
    (AyMPACConj completionFingerprint fingerprintAgreement)

def AyMPACAssignmentDigest
    (partialDigest completedDigest digestAgreement : Prop) : Prop :=
  AyMPACConj partialDigest (AyMPACConj completedDigest digestAgreement)

def AyMPACBuildEvidence
    (solverBuild completionBuild buildAgreement : Prop) : Prop :=
  AyMPACConj solverBuild (AyMPACConj completionBuild buildAgreement)

def AyMPACAcceptedCompletion
    (manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk : Prop) : Prop :=
  AyMPACConj manifestOk
    (AyMPACConj domainOk
      (AyMPACConj defaultOk
        (AyMPACConj mapsOk
          (AyMPACConj clauseReplayOk
            (AyMPACConj checkerOk
              (AyMPACConj fingerprintOk
                (AyMPACConj digestOk buildOk)))))))

def AyMPACPublicSatWitness
    (acceptedCompletion fullWitness publicSatClaim : Prop) : Prop :=
  AyMPACConj acceptedCompletion (AyMPACConj fullWitness publicSatClaim)

def AyMPACNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyMPACConj reason blocksPublication

def AyMPACRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyMPACConj reason recomputeRequested

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

theorem ay_mpac_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyMPACEquisat source target :=
  fun forward backward => ay_mpac_conj_intro forward backward

theorem ay_mpac_equisat_forward {source target : Prop} :
    AyMPACEquisat source target -> source -> target :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_equisat_backward {source target : Prop} :
    AyMPACEquisat source target -> target -> source :=
  fun h => ay_mpac_conj_right h

theorem ay_mpac_completion_manifest_intro
    {partialWitness completionPlan completedWitness : Prop} :
    partialWitness -> completionPlan -> completedWitness ->
    AyMPACCompletionManifest partialWitness completionPlan completedWitness :=
  fun hpartial hplan hcompleted =>
    ay_mpac_conj_intro hpartial (ay_mpac_conj_intro hplan hcompleted)

theorem ay_mpac_completion_manifest_partial
    {partialWitness completionPlan completedWitness : Prop} :
    AyMPACCompletionManifest partialWitness completionPlan completedWitness ->
    partialWitness :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_completion_manifest_plan
    {partialWitness completionPlan completedWitness : Prop} :
    AyMPACCompletionManifest partialWitness completionPlan completedWitness ->
    completionPlan :=
  fun h => ay_mpac_conj_left (ay_mpac_conj_right h)

theorem ay_mpac_completion_manifest_completed
    {partialWitness completionPlan completedWitness : Prop} :
    AyMPACCompletionManifest partialWitness completionPlan completedWitness ->
    completedWitness :=
  fun h => ay_mpac_conj_right (ay_mpac_conj_right h)

theorem ay_mpac_variable_domain_evidence_intro
    {originalDomain coveredDomain noMissingVariables : Prop} :
    originalDomain -> coveredDomain -> noMissingVariables ->
    AyMPACVariableDomainEvidence
      originalDomain coveredDomain noMissingVariables :=
  fun horiginal hcovered hmissing =>
    ay_mpac_conj_intro horiginal (ay_mpac_conj_intro hcovered hmissing)

theorem ay_mpac_variable_domain_no_missing
    {originalDomain coveredDomain noMissingVariables : Prop} :
    AyMPACVariableDomainEvidence
      originalDomain coveredDomain noMissingVariables ->
    noMissingVariables :=
  fun h => ay_mpac_conj_right (ay_mpac_conj_right h)

theorem ay_mpac_default_value_policy_intro
    {defaultPolicy defaultAssignments policyAgreement : Prop} :
    defaultPolicy -> defaultAssignments -> policyAgreement ->
    AyMPACDefaultValuePolicy
      defaultPolicy defaultAssignments policyAgreement :=
  fun hpolicy hdefaults hagree =>
    ay_mpac_conj_intro hpolicy (ay_mpac_conj_intro hdefaults hagree)

theorem ay_mpac_default_value_policy_agreement
    {defaultPolicy defaultAssignments policyAgreement : Prop} :
    AyMPACDefaultValuePolicy
      defaultPolicy defaultAssignments policyAgreement ->
    policyAgreement :=
  fun h => ay_mpac_conj_right (ay_mpac_conj_right h)

theorem ay_mpac_bidirectional_variable_maps_intro
    {solverToDimacs dimacsToSolver inverseAgreement : Prop} :
    solverToDimacs -> dimacsToSolver -> inverseAgreement ->
    AyMPACBidirectionalVariableMaps
      solverToDimacs dimacsToSolver inverseAgreement :=
  fun hforward hbackward hagree =>
    ay_mpac_conj_intro hforward (ay_mpac_conj_intro hbackward hagree)

theorem ay_mpac_bidirectional_variable_maps_forward
    {solverToDimacs dimacsToSolver inverseAgreement : Prop} :
    AyMPACBidirectionalVariableMaps
      solverToDimacs dimacsToSolver inverseAgreement ->
    solverToDimacs :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_bidirectional_variable_maps_backward
    {solverToDimacs dimacsToSolver inverseAgreement : Prop} :
    AyMPACBidirectionalVariableMaps
      solverToDimacs dimacsToSolver inverseAgreement ->
    dimacsToSolver :=
  fun h => ay_mpac_conj_left (ay_mpac_conj_right h)

theorem ay_mpac_bidirectional_variable_maps_agreement
    {solverToDimacs dimacsToSolver inverseAgreement : Prop} :
    AyMPACBidirectionalVariableMaps
      solverToDimacs dimacsToSolver inverseAgreement ->
    inverseAgreement :=
  fun h => ay_mpac_conj_right (ay_mpac_conj_right h)

theorem ay_mpac_clause_replay_intro
    {clauseReplay completedEvaluation replayAgreement : Prop} :
    clauseReplay -> completedEvaluation -> replayAgreement ->
    AyMPACClauseReplay clauseReplay completedEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_mpac_conj_intro hreplay (ay_mpac_conj_intro heval hagree)

theorem ay_mpac_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyMPACCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_mpac_conj_intro haccepted (ay_mpac_conj_intro htranscript hagree)

theorem ay_mpac_formula_fingerprint_intro
    {originalFingerprint completionFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> completionFingerprint -> fingerprintAgreement ->
    AyMPACFormulaFingerprint
      originalFingerprint completionFingerprint fingerprintAgreement :=
  fun horiginal hcompletion hagree =>
    ay_mpac_conj_intro horiginal (ay_mpac_conj_intro hcompletion hagree)

theorem ay_mpac_assignment_digest_intro
    {partialDigest completedDigest digestAgreement : Prop} :
    partialDigest -> completedDigest -> digestAgreement ->
    AyMPACAssignmentDigest partialDigest completedDigest digestAgreement :=
  fun hpartial hcompleted hagree =>
    ay_mpac_conj_intro hpartial (ay_mpac_conj_intro hcompleted hagree)

theorem ay_mpac_build_evidence_intro
    {solverBuild completionBuild buildAgreement : Prop} :
    solverBuild -> completionBuild -> buildAgreement ->
    AyMPACBuildEvidence solverBuild completionBuild buildAgreement :=
  fun hsolver hcompletion hagree =>
    ay_mpac_conj_intro hsolver (ay_mpac_conj_intro hcompletion hagree)

theorem ay_mpac_accepted_completion_intro
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk : Prop} :
    manifestOk -> domainOk -> defaultOk -> mapsOk -> clauseReplayOk ->
    checkerOk -> fingerprintOk -> digestOk -> buildOk ->
    AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
      clauseReplayOk checkerOk fingerprintOk digestOk buildOk :=
  fun hmanifest hdomain hdefault hmaps hclause hchecker hfingerprint
      hdigest hbuild =>
    ay_mpac_conj_intro hmanifest
      (ay_mpac_conj_intro hdomain
        (ay_mpac_conj_intro hdefault
          (ay_mpac_conj_intro hmaps
            (ay_mpac_conj_intro hclause
              (ay_mpac_conj_intro hchecker
                (ay_mpac_conj_intro hfingerprint
                  (ay_mpac_conj_intro hdigest hbuild)))))))

theorem ay_mpac_accepted_completion_manifest
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk : Prop} :
    AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
      clauseReplayOk checkerOk fingerprintOk digestOk buildOk ->
    manifestOk :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_accepted_completion_domain
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk : Prop} :
    AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
      clauseReplayOk checkerOk fingerprintOk digestOk buildOk ->
    domainOk :=
  fun h => ay_mpac_conj_left (ay_mpac_conj_right h)

theorem ay_mpac_accepted_completion_default
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk : Prop} :
    AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
      clauseReplayOk checkerOk fingerprintOk digestOk buildOk ->
    defaultOk :=
  fun h => ay_mpac_conj_left (ay_mpac_conj_right (ay_mpac_conj_right h))

theorem ay_mpac_accepted_completion_maps
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk : Prop} :
    AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
      clauseReplayOk checkerOk fingerprintOk digestOk buildOk ->
    mapsOk :=
  fun h =>
    ay_mpac_conj_left
      (ay_mpac_conj_right (ay_mpac_conj_right (ay_mpac_conj_right h)))

theorem ay_mpac_accepted_completion_clause_replay
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk : Prop} :
    AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
      clauseReplayOk checkerOk fingerprintOk digestOk buildOk ->
    clauseReplayOk :=
  fun h =>
    ay_mpac_conj_left
      (ay_mpac_conj_right
        (ay_mpac_conj_right (ay_mpac_conj_right (ay_mpac_conj_right h))))

theorem ay_mpac_accepted_completion_checker
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk : Prop} :
    AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
      clauseReplayOk checkerOk fingerprintOk digestOk buildOk ->
    checkerOk :=
  fun h =>
    ay_mpac_conj_left
      (ay_mpac_conj_right
        (ay_mpac_conj_right
          (ay_mpac_conj_right (ay_mpac_conj_right (ay_mpac_conj_right h)))))

theorem ay_mpac_accepted_completion_fingerprint
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk : Prop} :
    AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
      clauseReplayOk checkerOk fingerprintOk digestOk buildOk ->
    fingerprintOk :=
  fun h =>
    ay_mpac_conj_left
      (ay_mpac_conj_right
        (ay_mpac_conj_right
          (ay_mpac_conj_right
            (ay_mpac_conj_right (ay_mpac_conj_right
              (ay_mpac_conj_right h))))))

theorem ay_mpac_accepted_completion_digest
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk : Prop} :
    AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
      clauseReplayOk checkerOk fingerprintOk digestOk buildOk ->
    digestOk :=
  fun h =>
    ay_mpac_conj_left
      (ay_mpac_conj_right
        (ay_mpac_conj_right
          (ay_mpac_conj_right
            (ay_mpac_conj_right
              (ay_mpac_conj_right (ay_mpac_conj_right
                (ay_mpac_conj_right h)))))))

theorem ay_mpac_accepted_completion_build
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk : Prop} :
    AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
      clauseReplayOk checkerOk fingerprintOk digestOk buildOk ->
    buildOk :=
  fun h =>
    ay_mpac_conj_right
      (ay_mpac_conj_right
        (ay_mpac_conj_right
          (ay_mpac_conj_right
            (ay_mpac_conj_right
              (ay_mpac_conj_right (ay_mpac_conj_right
                (ay_mpac_conj_right h)))))))

theorem ay_mpac_public_sat_witness_intro
    {acceptedCompletion fullWitness publicSatClaim : Prop} :
    acceptedCompletion -> fullWitness -> publicSatClaim ->
    AyMPACPublicSatWitness acceptedCompletion fullWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mpac_conj_intro hevidence (ay_mpac_conj_intro hwitness hclaim)

theorem ay_mpac_public_sat_witness_evidence
    {acceptedCompletion fullWitness publicSatClaim : Prop} :
    AyMPACPublicSatWitness acceptedCompletion fullWitness publicSatClaim ->
    acceptedCompletion :=
  fun h => ay_mpac_conj_left h

theorem ay_mpac_public_sat_witness_claim
    {acceptedCompletion fullWitness publicSatClaim : Prop} :
    AyMPACPublicSatWitness acceptedCompletion fullWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mpac_conj_right (ay_mpac_conj_right h)

theorem ay_mpac_accepted_completion_publishes_sound_sat
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk fullWitness publicSatClaim : Prop} :
    AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
      clauseReplayOk checkerOk fingerprintOk digestOk buildOk ->
    fullWitness -> publicSatClaim ->
    AyMPACPublicSatWitness
      (AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
        clauseReplayOk checkerOk fingerprintOk digestOk buildOk)
      fullWitness publicSatClaim :=
  ay_mpac_public_sat_witness_intro

theorem ay_mpac_completion_preserves_truth
    {partialTruth fullTruth : Prop} :
    AyMPACEquisat partialTruth fullTruth -> partialTruth -> fullTruth :=
  ay_mpac_equisat_forward

theorem ay_mpac_public_sat_requires_accepted_completion
    {acceptedCompletion fullWitness publicSatClaim : Prop} :
    AyMPACPublicSatWitness acceptedCompletion fullWitness publicSatClaim ->
    acceptedCompletion :=
  ay_mpac_public_sat_witness_evidence

theorem ay_mpac_publication_requires_domain
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk fullWitness publicSatClaim : Prop} :
    AyMPACPublicSatWitness
      (AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
        clauseReplayOk checkerOk fingerprintOk digestOk buildOk)
      fullWitness publicSatClaim ->
    domainOk :=
  fun h =>
    ay_mpac_accepted_completion_domain
      (ay_mpac_public_sat_witness_evidence h)

theorem ay_mpac_publication_requires_defaults
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk fullWitness publicSatClaim : Prop} :
    AyMPACPublicSatWitness
      (AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
        clauseReplayOk checkerOk fingerprintOk digestOk buildOk)
      fullWitness publicSatClaim ->
    defaultOk :=
  fun h =>
    ay_mpac_accepted_completion_default
      (ay_mpac_public_sat_witness_evidence h)

theorem ay_mpac_publication_requires_maps
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk fullWitness publicSatClaim : Prop} :
    AyMPACPublicSatWitness
      (AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
        clauseReplayOk checkerOk fingerprintOk digestOk buildOk)
      fullWitness publicSatClaim ->
    mapsOk :=
  fun h =>
    ay_mpac_accepted_completion_maps
      (ay_mpac_public_sat_witness_evidence h)

theorem ay_mpac_publication_requires_clause_replay
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk fullWitness publicSatClaim : Prop} :
    AyMPACPublicSatWitness
      (AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
        clauseReplayOk checkerOk fingerprintOk digestOk buildOk)
      fullWitness publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_mpac_accepted_completion_clause_replay
      (ay_mpac_public_sat_witness_evidence h)

theorem ay_mpac_publication_requires_checker
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk fullWitness publicSatClaim : Prop} :
    AyMPACPublicSatWitness
      (AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
        clauseReplayOk checkerOk fingerprintOk digestOk buildOk)
      fullWitness publicSatClaim ->
    checkerOk :=
  fun h =>
    ay_mpac_accepted_completion_checker
      (ay_mpac_public_sat_witness_evidence h)

theorem ay_mpac_publication_requires_fingerprint
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk fullWitness publicSatClaim : Prop} :
    AyMPACPublicSatWitness
      (AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
        clauseReplayOk checkerOk fingerprintOk digestOk buildOk)
      fullWitness publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mpac_accepted_completion_fingerprint
      (ay_mpac_public_sat_witness_evidence h)

theorem ay_mpac_publication_requires_digest
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk fullWitness publicSatClaim : Prop} :
    AyMPACPublicSatWitness
      (AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
        clauseReplayOk checkerOk fingerprintOk digestOk buildOk)
      fullWitness publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mpac_accepted_completion_digest
      (ay_mpac_public_sat_witness_evidence h)

theorem ay_mpac_publication_requires_build
    {manifestOk domainOk defaultOk mapsOk clauseReplayOk checkerOk
      fingerprintOk digestOk buildOk fullWitness publicSatClaim : Prop} :
    AyMPACPublicSatWitness
      (AyMPACAcceptedCompletion manifestOk domainOk defaultOk mapsOk
        clauseReplayOk checkerOk fingerprintOk digestOk buildOk)
      fullWitness publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mpac_accepted_completion_build
      (ay_mpac_public_sat_witness_evidence h)

theorem ay_mpac_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyMPACNoClaimDiagnostic reason blocksPublication :=
  ay_mpac_conj_intro

theorem ay_mpac_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyMPACNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_mpac_conj_right

theorem ay_mpac_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyMPACRecomputeObligation reason recomputeRequested :=
  ay_mpac_conj_intro

theorem ay_mpac_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyMPACRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_mpac_conj_right

theorem ay_mpac_missing_domain_coverage_no_claim
    {missingDomainCoverage blocksPublication : Prop} :
    missingDomainCoverage -> blocksPublication ->
    AyMPACNoClaimDiagnostic missingDomainCoverage blocksPublication :=
  ay_mpac_no_claim_diagnostic_intro

theorem ay_mpac_missing_domain_coverage_recompute
    {missingDomainCoverage recomputeRequested : Prop} :
    missingDomainCoverage -> recomputeRequested ->
    AyMPACRecomputeObligation missingDomainCoverage recomputeRequested :=
  ay_mpac_recompute_obligation_intro

theorem ay_mpac_map_mismatch_no_claim
    {mapMismatch blocksPublication : Prop} :
    mapMismatch -> blocksPublication ->
    AyMPACNoClaimDiagnostic mapMismatch blocksPublication :=
  ay_mpac_no_claim_diagnostic_intro

theorem ay_mpac_default_policy_drift_no_claim
    {defaultPolicyDrift blocksPublication : Prop} :
    defaultPolicyDrift -> blocksPublication ->
    AyMPACNoClaimDiagnostic defaultPolicyDrift blocksPublication :=
  ay_mpac_no_claim_diagnostic_intro

theorem ay_mpac_digest_drift_no_claim
    {digestDrift blocksPublication : Prop} :
    digestDrift -> blocksPublication ->
    AyMPACNoClaimDiagnostic digestDrift blocksPublication :=
  ay_mpac_no_claim_diagnostic_intro

theorem ay_mpac_clause_replay_gap_no_claim
    {clauseReplayGap blocksPublication : Prop} :
    clauseReplayGap -> blocksPublication ->
    AyMPACNoClaimDiagnostic clauseReplayGap blocksPublication :=
  ay_mpac_no_claim_diagnostic_intro

theorem ay_mpac_stale_fingerprint_no_claim
    {staleFingerprint blocksPublication : Prop} :
    staleFingerprint -> blocksPublication ->
    AyMPACNoClaimDiagnostic staleFingerprint blocksPublication :=
  ay_mpac_no_claim_diagnostic_intro

theorem ay_mpac_checker_reject_no_claim
    {checkerReject blocksPublication : Prop} :
    checkerReject -> blocksPublication ->
    AyMPACNoClaimDiagnostic checkerReject blocksPublication :=
  ay_mpac_no_claim_diagnostic_intro

theorem ay_mpac_build_drift_no_claim
    {buildDrift blocksPublication : Prop} :
    buildDrift -> blocksPublication ->
    AyMPACNoClaimDiagnostic buildDrift blocksPublication :=
  ay_mpac_no_claim_diagnostic_intro

theorem ay_mpac_bad_completion_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyMPACNoClaimDiagnostic failure blocksPublication ->
    AyMPACRecomputeObligation failure recomputeRequested ->
    AyMPACConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_mpac_conj_intro
      (ay_mpac_no_claim_diagnostic_blocks hdiagnostic)
      (ay_mpac_recompute_obligation_request hrecompute)
