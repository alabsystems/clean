/- SAT-COMP/ay incremental witness-cache epoch contract.

This package models when cached SAT witness fragments may be reused in
sequential-main SAT-COMP output.  Reuse is gated by cache epoch, digest, domain,
DIMACS map, completion, replay, checker, fingerprint, and build evidence.
-/

def AyMIWCConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMIWCDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMIWCEquisat (source target : Prop) : Prop :=
  AyMIWCConj (source -> target) (target -> source)

def AyMIWCWitnessCacheEpochLedger
    (cacheEpoch fragmentEpoch epochAgreement : Prop) : Prop :=
  AyMIWCConj cacheEpoch (AyMIWCConj fragmentEpoch epochAgreement)

def AyMIWCAssignmentDigest
    (fragmentDigest assignmentDigest digestAgreement : Prop) : Prop :=
  AyMIWCConj fragmentDigest (AyMIWCConj assignmentDigest digestAgreement)

def AyMIWCVariableDomainManifest
    (cachedDomain originalDomain domainAgreement : Prop) : Prop :=
  AyMIWCConj cachedDomain (AyMIWCConj originalDomain domainAgreement)

def AyMIWCDimacsMaps
    (cacheToDimacs dimacsToCache mapAgreement : Prop) : Prop :=
  AyMIWCConj cacheToDimacs (AyMIWCConj dimacsToCache mapAgreement)

def AyMIWCCompletionManifest
    (fragmentWitness completedWitness completionAgreement : Prop) : Prop :=
  AyMIWCConj fragmentWitness
    (AyMIWCConj completedWitness completionAgreement)

def AyMIWCClauseReplay
    (clauseReplay witnessEvaluation replayAgreement : Prop) : Prop :=
  AyMIWCConj clauseReplay (AyMIWCConj witnessEvaluation replayAgreement)

def AyMIWCCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyMIWCConj checkerAccepted (AyMIWCConj transcript transcriptAgreement)

def AyMIWCFormulaFingerprint
    (originalFingerprint cacheFingerprint fingerprintAgreement : Prop) : Prop :=
  AyMIWCConj originalFingerprint
    (AyMIWCConj cacheFingerprint fingerprintAgreement)

def AyMIWCBuildEvidence
    (solverBuild cacheBuild buildAgreement : Prop) : Prop :=
  AyMIWCConj solverBuild (AyMIWCConj cacheBuild buildAgreement)

def AyMIWCAcceptedReuse
    (epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop) : Prop :=
  AyMIWCConj epochOk
    (AyMIWCConj digestOk
      (AyMIWCConj domainOk
        (AyMIWCConj mapsOk
          (AyMIWCConj completionOk
            (AyMIWCConj clauseReplayOk
              (AyMIWCConj checkerOk
                (AyMIWCConj fingerprintOk buildOk)))))))

def AyMIWCPublicSatWitness
    (acceptedReuse cachedWitness publicSatClaim : Prop) : Prop :=
  AyMIWCConj acceptedReuse (AyMIWCConj cachedWitness publicSatClaim)

def AyMIWCNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyMIWCConj reason blocksPublication

def AyMIWCRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyMIWCConj reason recomputeRequested

theorem ay_miwc_conj_intro {left right : Prop} :
    left -> right -> AyMIWCConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_miwc_conj_left {left right : Prop} :
    AyMIWCConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_miwc_conj_right {left right : Prop} :
    AyMIWCConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_miwc_disj_left {left right : Prop} :
    left -> AyMIWCDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_miwc_disj_right {left right : Prop} :
    right -> AyMIWCDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_miwc_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyMIWCEquisat source target :=
  fun forward backward => ay_miwc_conj_intro forward backward

theorem ay_miwc_equisat_forward {source target : Prop} :
    AyMIWCEquisat source target -> source -> target :=
  fun h => ay_miwc_conj_left h

theorem ay_miwc_equisat_backward {source target : Prop} :
    AyMIWCEquisat source target -> target -> source :=
  fun h => ay_miwc_conj_right h

theorem ay_miwc_witness_cache_epoch_ledger_intro
    {cacheEpoch fragmentEpoch epochAgreement : Prop} :
    cacheEpoch -> fragmentEpoch -> epochAgreement ->
    AyMIWCWitnessCacheEpochLedger
      cacheEpoch fragmentEpoch epochAgreement :=
  fun hcache hfragment hagree =>
    ay_miwc_conj_intro hcache (ay_miwc_conj_intro hfragment hagree)

theorem ay_miwc_witness_cache_epoch_cache
    {cacheEpoch fragmentEpoch epochAgreement : Prop} :
    AyMIWCWitnessCacheEpochLedger
      cacheEpoch fragmentEpoch epochAgreement ->
    cacheEpoch :=
  fun h => ay_miwc_conj_left h

theorem ay_miwc_witness_cache_epoch_fragment
    {cacheEpoch fragmentEpoch epochAgreement : Prop} :
    AyMIWCWitnessCacheEpochLedger
      cacheEpoch fragmentEpoch epochAgreement ->
    fragmentEpoch :=
  fun h => ay_miwc_conj_left (ay_miwc_conj_right h)

theorem ay_miwc_witness_cache_epoch_agreement
    {cacheEpoch fragmentEpoch epochAgreement : Prop} :
    AyMIWCWitnessCacheEpochLedger
      cacheEpoch fragmentEpoch epochAgreement ->
    epochAgreement :=
  fun h => ay_miwc_conj_right (ay_miwc_conj_right h)

theorem ay_miwc_assignment_digest_intro
    {fragmentDigest assignmentDigest digestAgreement : Prop} :
    fragmentDigest -> assignmentDigest -> digestAgreement ->
    AyMIWCAssignmentDigest fragmentDigest assignmentDigest digestAgreement :=
  fun hfragment hassignment hagree =>
    ay_miwc_conj_intro hfragment (ay_miwc_conj_intro hassignment hagree)

theorem ay_miwc_variable_domain_manifest_intro
    {cachedDomain originalDomain domainAgreement : Prop} :
    cachedDomain -> originalDomain -> domainAgreement ->
    AyMIWCVariableDomainManifest
      cachedDomain originalDomain domainAgreement :=
  fun hcached horiginal hagree =>
    ay_miwc_conj_intro hcached (ay_miwc_conj_intro horiginal hagree)

theorem ay_miwc_dimacs_maps_intro
    {cacheToDimacs dimacsToCache mapAgreement : Prop} :
    cacheToDimacs -> dimacsToCache -> mapAgreement ->
    AyMIWCDimacsMaps cacheToDimacs dimacsToCache mapAgreement :=
  fun hforward hbackward hagree =>
    ay_miwc_conj_intro hforward (ay_miwc_conj_intro hbackward hagree)

theorem ay_miwc_completion_manifest_intro
    {fragmentWitness completedWitness completionAgreement : Prop} :
    fragmentWitness -> completedWitness -> completionAgreement ->
    AyMIWCCompletionManifest
      fragmentWitness completedWitness completionAgreement :=
  fun hfragment hcompleted hagree =>
    ay_miwc_conj_intro hfragment (ay_miwc_conj_intro hcompleted hagree)

theorem ay_miwc_clause_replay_intro
    {clauseReplay witnessEvaluation replayAgreement : Prop} :
    clauseReplay -> witnessEvaluation -> replayAgreement ->
    AyMIWCClauseReplay clauseReplay witnessEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_miwc_conj_intro hreplay (ay_miwc_conj_intro heval hagree)

theorem ay_miwc_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyMIWCCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_miwc_conj_intro haccepted (ay_miwc_conj_intro htranscript hagree)

theorem ay_miwc_formula_fingerprint_intro
    {originalFingerprint cacheFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> cacheFingerprint -> fingerprintAgreement ->
    AyMIWCFormulaFingerprint
      originalFingerprint cacheFingerprint fingerprintAgreement :=
  fun horiginal hcache hagree =>
    ay_miwc_conj_intro horiginal (ay_miwc_conj_intro hcache hagree)

theorem ay_miwc_build_evidence_intro
    {solverBuild cacheBuild buildAgreement : Prop} :
    solverBuild -> cacheBuild -> buildAgreement ->
    AyMIWCBuildEvidence solverBuild cacheBuild buildAgreement :=
  fun hsolver hcache hagree =>
    ay_miwc_conj_intro hsolver (ay_miwc_conj_intro hcache hagree)

theorem ay_miwc_accepted_reuse_intro
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    epochOk -> digestOk -> domainOk -> mapsOk -> completionOk ->
    clauseReplayOk -> checkerOk -> fingerprintOk -> buildOk ->
    AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk :=
  fun hepoch hdigest hdomain hmaps hcompletion hclause hchecker
      hfingerprint hbuild =>
    ay_miwc_conj_intro hepoch
      (ay_miwc_conj_intro hdigest
        (ay_miwc_conj_intro hdomain
          (ay_miwc_conj_intro hmaps
            (ay_miwc_conj_intro hcompletion
              (ay_miwc_conj_intro hclause
                (ay_miwc_conj_intro hchecker
                  (ay_miwc_conj_intro hfingerprint hbuild)))))))

theorem ay_miwc_accepted_reuse_epoch
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    epochOk :=
  fun h => ay_miwc_conj_left h

theorem ay_miwc_accepted_reuse_digest
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    digestOk :=
  fun h => ay_miwc_conj_left (ay_miwc_conj_right h)

theorem ay_miwc_accepted_reuse_domain
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    domainOk :=
  fun h => ay_miwc_conj_left (ay_miwc_conj_right (ay_miwc_conj_right h))

theorem ay_miwc_accepted_reuse_maps
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    mapsOk :=
  fun h =>
    ay_miwc_conj_left
      (ay_miwc_conj_right (ay_miwc_conj_right (ay_miwc_conj_right h)))

theorem ay_miwc_accepted_reuse_completion
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    completionOk :=
  fun h =>
    ay_miwc_conj_left
      (ay_miwc_conj_right
        (ay_miwc_conj_right (ay_miwc_conj_right (ay_miwc_conj_right h))))

theorem ay_miwc_accepted_reuse_clause_replay
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    clauseReplayOk :=
  fun h =>
    ay_miwc_conj_left
      (ay_miwc_conj_right
        (ay_miwc_conj_right
          (ay_miwc_conj_right (ay_miwc_conj_right (ay_miwc_conj_right h)))))

theorem ay_miwc_accepted_reuse_checker
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    checkerOk :=
  fun h =>
    ay_miwc_conj_left
      (ay_miwc_conj_right
        (ay_miwc_conj_right
          (ay_miwc_conj_right
            (ay_miwc_conj_right (ay_miwc_conj_right
              (ay_miwc_conj_right h))))))

theorem ay_miwc_accepted_reuse_fingerprint
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    fingerprintOk :=
  fun h =>
    ay_miwc_conj_left
      (ay_miwc_conj_right
        (ay_miwc_conj_right
          (ay_miwc_conj_right
            (ay_miwc_conj_right
              (ay_miwc_conj_right (ay_miwc_conj_right
                (ay_miwc_conj_right h)))))))

theorem ay_miwc_accepted_reuse_build
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk : Prop} :
    AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    buildOk :=
  fun h =>
    ay_miwc_conj_right
      (ay_miwc_conj_right
        (ay_miwc_conj_right
          (ay_miwc_conj_right
            (ay_miwc_conj_right
              (ay_miwc_conj_right (ay_miwc_conj_right
                (ay_miwc_conj_right h)))))))

theorem ay_miwc_public_sat_witness_intro
    {acceptedReuse cachedWitness publicSatClaim : Prop} :
    acceptedReuse -> cachedWitness -> publicSatClaim ->
    AyMIWCPublicSatWitness acceptedReuse cachedWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_miwc_conj_intro hevidence (ay_miwc_conj_intro hwitness hclaim)

theorem ay_miwc_public_sat_witness_evidence
    {acceptedReuse cachedWitness publicSatClaim : Prop} :
    AyMIWCPublicSatWitness acceptedReuse cachedWitness publicSatClaim ->
    acceptedReuse :=
  fun h => ay_miwc_conj_left h

theorem ay_miwc_public_sat_witness_claim
    {acceptedReuse cachedWitness publicSatClaim : Prop} :
    AyMIWCPublicSatWitness acceptedReuse cachedWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_miwc_conj_right (ay_miwc_conj_right h)

theorem ay_miwc_accepted_cache_epoch_reuse_publishes_sound_sat
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk cachedWitness publicSatClaim : Prop} :
    AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
      clauseReplayOk checkerOk fingerprintOk buildOk ->
    cachedWitness -> publicSatClaim ->
    AyMIWCPublicSatWitness
      (AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      cachedWitness publicSatClaim :=
  ay_miwc_public_sat_witness_intro

theorem ay_miwc_cache_fragment_reuse_preserves_truth
    {fragmentTruth publicTruth : Prop} :
    AyMIWCEquisat fragmentTruth publicTruth -> fragmentTruth -> publicTruth :=
  ay_miwc_equisat_forward

theorem ay_miwc_public_sat_requires_accepted_reuse
    {acceptedReuse cachedWitness publicSatClaim : Prop} :
    AyMIWCPublicSatWitness acceptedReuse cachedWitness publicSatClaim ->
    acceptedReuse :=
  ay_miwc_public_sat_witness_evidence

theorem ay_miwc_publication_requires_epoch
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk cachedWitness publicSatClaim : Prop} :
    AyMIWCPublicSatWitness
      (AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      cachedWitness publicSatClaim ->
    epochOk :=
  fun h => ay_miwc_accepted_reuse_epoch
    (ay_miwc_public_sat_witness_evidence h)

theorem ay_miwc_publication_requires_digest
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk cachedWitness publicSatClaim : Prop} :
    AyMIWCPublicSatWitness
      (AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      cachedWitness publicSatClaim ->
    digestOk :=
  fun h => ay_miwc_accepted_reuse_digest
    (ay_miwc_public_sat_witness_evidence h)

theorem ay_miwc_publication_requires_domain
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk cachedWitness publicSatClaim : Prop} :
    AyMIWCPublicSatWitness
      (AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      cachedWitness publicSatClaim ->
    domainOk :=
  fun h => ay_miwc_accepted_reuse_domain
    (ay_miwc_public_sat_witness_evidence h)

theorem ay_miwc_publication_requires_maps
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk cachedWitness publicSatClaim : Prop} :
    AyMIWCPublicSatWitness
      (AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      cachedWitness publicSatClaim ->
    mapsOk :=
  fun h => ay_miwc_accepted_reuse_maps
    (ay_miwc_public_sat_witness_evidence h)

theorem ay_miwc_publication_requires_completion
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk cachedWitness publicSatClaim : Prop} :
    AyMIWCPublicSatWitness
      (AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      cachedWitness publicSatClaim ->
    completionOk :=
  fun h => ay_miwc_accepted_reuse_completion
    (ay_miwc_public_sat_witness_evidence h)

theorem ay_miwc_publication_requires_clause_replay
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk cachedWitness publicSatClaim : Prop} :
    AyMIWCPublicSatWitness
      (AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      cachedWitness publicSatClaim ->
    clauseReplayOk :=
  fun h => ay_miwc_accepted_reuse_clause_replay
    (ay_miwc_public_sat_witness_evidence h)

theorem ay_miwc_publication_requires_checker
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk cachedWitness publicSatClaim : Prop} :
    AyMIWCPublicSatWitness
      (AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      cachedWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_miwc_accepted_reuse_checker
    (ay_miwc_public_sat_witness_evidence h)

theorem ay_miwc_publication_requires_fingerprint
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk cachedWitness publicSatClaim : Prop} :
    AyMIWCPublicSatWitness
      (AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      cachedWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_miwc_accepted_reuse_fingerprint
    (ay_miwc_public_sat_witness_evidence h)

theorem ay_miwc_publication_requires_build
    {epochOk digestOk domainOk mapsOk completionOk clauseReplayOk checkerOk
      fingerprintOk buildOk cachedWitness publicSatClaim : Prop} :
    AyMIWCPublicSatWitness
      (AyMIWCAcceptedReuse epochOk digestOk domainOk mapsOk completionOk
        clauseReplayOk checkerOk fingerprintOk buildOk)
      cachedWitness publicSatClaim ->
    buildOk :=
  fun h => ay_miwc_accepted_reuse_build
    (ay_miwc_public_sat_witness_evidence h)

theorem ay_miwc_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyMIWCNoClaimDiagnostic reason blocksPublication :=
  ay_miwc_conj_intro

theorem ay_miwc_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyMIWCNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_miwc_conj_right

theorem ay_miwc_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyMIWCRecomputeObligation reason recomputeRequested :=
  ay_miwc_conj_intro

theorem ay_miwc_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyMIWCRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_miwc_conj_right

theorem ay_miwc_cache_epoch_drift_no_claim
    {cacheEpochDrift blocksPublication : Prop} :
    cacheEpochDrift -> blocksPublication ->
    AyMIWCNoClaimDiagnostic cacheEpochDrift blocksPublication :=
  ay_miwc_no_claim_diagnostic_intro

theorem ay_miwc_cache_epoch_drift_recompute
    {cacheEpochDrift recomputeRequested : Prop} :
    cacheEpochDrift -> recomputeRequested ->
    AyMIWCRecomputeObligation cacheEpochDrift recomputeRequested :=
  ay_miwc_recompute_obligation_intro

theorem ay_miwc_stale_fragment_no_claim
    {staleFragment blocksPublication : Prop} :
    staleFragment -> blocksPublication ->
    AyMIWCNoClaimDiagnostic staleFragment blocksPublication :=
  ay_miwc_no_claim_diagnostic_intro

theorem ay_miwc_digest_drift_no_claim
    {digestDrift blocksPublication : Prop} :
    digestDrift -> blocksPublication ->
    AyMIWCNoClaimDiagnostic digestDrift blocksPublication :=
  ay_miwc_no_claim_diagnostic_intro

theorem ay_miwc_domain_mismatch_no_claim
    {domainMismatch blocksPublication : Prop} :
    domainMismatch -> blocksPublication ->
    AyMIWCNoClaimDiagnostic domainMismatch blocksPublication :=
  ay_miwc_no_claim_diagnostic_intro

theorem ay_miwc_map_mismatch_no_claim
    {mapMismatch blocksPublication : Prop} :
    mapMismatch -> blocksPublication ->
    AyMIWCNoClaimDiagnostic mapMismatch blocksPublication :=
  ay_miwc_no_claim_diagnostic_intro

theorem ay_miwc_completion_mismatch_no_claim
    {completionMismatch blocksPublication : Prop} :
    completionMismatch -> blocksPublication ->
    AyMIWCNoClaimDiagnostic completionMismatch blocksPublication :=
  ay_miwc_no_claim_diagnostic_intro

theorem ay_miwc_clause_replay_gap_no_claim
    {clauseReplayGap blocksPublication : Prop} :
    clauseReplayGap -> blocksPublication ->
    AyMIWCNoClaimDiagnostic clauseReplayGap blocksPublication :=
  ay_miwc_no_claim_diagnostic_intro

theorem ay_miwc_stale_fingerprint_no_claim
    {staleFingerprint blocksPublication : Prop} :
    staleFingerprint -> blocksPublication ->
    AyMIWCNoClaimDiagnostic staleFingerprint blocksPublication :=
  ay_miwc_no_claim_diagnostic_intro

theorem ay_miwc_checker_reject_no_claim
    {checkerReject blocksPublication : Prop} :
    checkerReject -> blocksPublication ->
    AyMIWCNoClaimDiagnostic checkerReject blocksPublication :=
  ay_miwc_no_claim_diagnostic_intro

theorem ay_miwc_build_drift_no_claim
    {buildDrift blocksPublication : Prop} :
    buildDrift -> blocksPublication ->
    AyMIWCNoClaimDiagnostic buildDrift blocksPublication :=
  ay_miwc_no_claim_diagnostic_intro

theorem ay_miwc_bad_cache_reuse_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyMIWCNoClaimDiagnostic failure blocksPublication ->
    AyMIWCRecomputeObligation failure recomputeRequested ->
    AyMIWCConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_miwc_conj_intro
      (ay_miwc_no_claim_diagnostic_blocks hdiagnostic)
      (ay_miwc_recompute_obligation_request hrecompute)
