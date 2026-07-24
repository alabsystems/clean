/- SAT-COMP/ay model certificate bundle roundtrip contract.

The package is propositional and self-contained.  It records the evidence gates
for accepting a bundled SAT model certificate and the diagnostic gates that
prevent stale or malformed bundles from blessing public SAT output.
-/

def AyMCBRConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMCBRDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMCBREquisat (source target : Prop) : Prop :=
  AyMCBRConj (source -> target) (target -> source)

def AyMCBRCompressedWitnessChunks
    (bundleManifest chunkSet chunkOrder : Prop) : Prop :=
  AyMCBRConj bundleManifest (AyMCBRConj chunkSet chunkOrder)

def AyMCBRAssignmentDigest
    (bundleDigest assignmentDigest digestAgreement : Prop) : Prop :=
  AyMCBRConj bundleDigest (AyMCBRConj assignmentDigest digestAgreement)

def AyMCBRDimacsMaps
    (bundleMap dimacsMap mapAgreement : Prop) : Prop :=
  AyMCBRConj bundleMap (AyMCBRConj dimacsMap mapAgreement)

def AyMCBRClauseReplayTranscript
    (clauseReplay replayTranscript replayAgreement : Prop) : Prop :=
  AyMCBRConj clauseReplay (AyMCBRConj replayTranscript replayAgreement)

def AyMCBRCheckerTranscript
    (checkerAccepted checkerTranscript checkerAgreement : Prop) : Prop :=
  AyMCBRConj checkerAccepted
    (AyMCBRConj checkerTranscript checkerAgreement)

def AyMCBRFormulaFingerprint
    (originalFingerprint bundleFingerprint fingerprintAgreement : Prop) : Prop :=
  AyMCBRConj originalFingerprint
    (AyMCBRConj bundleFingerprint fingerprintAgreement)

def AyMCBRBuildEvidence
    (solverBuild bundleBuild buildAgreement : Prop) : Prop :=
  AyMCBRConj solverBuild (AyMCBRConj bundleBuild buildAgreement)

def AyMCBRRoundtripEvidence
    (chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop) : Prop :=
  AyMCBRConj chunksOk
    (AyMCBRConj digestOk
      (AyMCBRConj mapsOk
        (AyMCBRConj clauseReplayOk
          (AyMCBRConj checkerOk
            (AyMCBRConj fingerprintOk buildOk)))))

def AyMCBRPublicSatWitness
    (roundtripEvidence publicWitness publicSatClaim : Prop) : Prop :=
  AyMCBRConj roundtripEvidence (AyMCBRConj publicWitness publicSatClaim)

def AyMCBRNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyMCBRConj reason blocksPublication

def AyMCBRRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyMCBRConj reason recomputeRequested

theorem ay_mcbr_conj_intro {left right : Prop} :
    left -> right -> AyMCBRConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mcbr_conj_left {left right : Prop} :
    AyMCBRConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mcbr_conj_right {left right : Prop} :
    AyMCBRConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mcbr_disj_left {left right : Prop} :
    left -> AyMCBRDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mcbr_disj_right {left right : Prop} :
    right -> AyMCBRDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mcbr_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyMCBREquisat source target :=
  fun forward backward => ay_mcbr_conj_intro forward backward

theorem ay_mcbr_equisat_forward {source target : Prop} :
    AyMCBREquisat source target -> source -> target :=
  fun h => ay_mcbr_conj_left h

theorem ay_mcbr_equisat_backward {source target : Prop} :
    AyMCBREquisat source target -> target -> source :=
  fun h => ay_mcbr_conj_right h

theorem ay_mcbr_compressed_witness_chunks_intro
    {bundleManifest chunkSet chunkOrder : Prop} :
    bundleManifest -> chunkSet -> chunkOrder ->
    AyMCBRCompressedWitnessChunks bundleManifest chunkSet chunkOrder :=
  fun hmanifest hchunks horder =>
    ay_mcbr_conj_intro hmanifest (ay_mcbr_conj_intro hchunks horder)

theorem ay_mcbr_compressed_witness_chunks_manifest
    {bundleManifest chunkSet chunkOrder : Prop} :
    AyMCBRCompressedWitnessChunks bundleManifest chunkSet chunkOrder ->
    bundleManifest :=
  fun h => ay_mcbr_conj_left h

theorem ay_mcbr_compressed_witness_chunks_set
    {bundleManifest chunkSet chunkOrder : Prop} :
    AyMCBRCompressedWitnessChunks bundleManifest chunkSet chunkOrder ->
    chunkSet :=
  fun h => ay_mcbr_conj_left (ay_mcbr_conj_right h)

theorem ay_mcbr_compressed_witness_chunks_order
    {bundleManifest chunkSet chunkOrder : Prop} :
    AyMCBRCompressedWitnessChunks bundleManifest chunkSet chunkOrder ->
    chunkOrder :=
  fun h => ay_mcbr_conj_right (ay_mcbr_conj_right h)

theorem ay_mcbr_assignment_digest_intro
    {bundleDigest assignmentDigest digestAgreement : Prop} :
    bundleDigest -> assignmentDigest -> digestAgreement ->
    AyMCBRAssignmentDigest bundleDigest assignmentDigest digestAgreement :=
  fun hbundle hassignment hagree =>
    ay_mcbr_conj_intro hbundle (ay_mcbr_conj_intro hassignment hagree)

theorem ay_mcbr_dimacs_maps_intro
    {bundleMap dimacsMap mapAgreement : Prop} :
    bundleMap -> dimacsMap -> mapAgreement ->
    AyMCBRDimacsMaps bundleMap dimacsMap mapAgreement :=
  fun hbundle hdimacs hagree =>
    ay_mcbr_conj_intro hbundle (ay_mcbr_conj_intro hdimacs hagree)

theorem ay_mcbr_clause_replay_transcript_intro
    {clauseReplay replayTranscript replayAgreement : Prop} :
    clauseReplay -> replayTranscript -> replayAgreement ->
    AyMCBRClauseReplayTranscript
      clauseReplay replayTranscript replayAgreement :=
  fun hreplay htranscript hagree =>
    ay_mcbr_conj_intro hreplay (ay_mcbr_conj_intro htranscript hagree)

theorem ay_mcbr_checker_transcript_intro
    {checkerAccepted checkerTranscript checkerAgreement : Prop} :
    checkerAccepted -> checkerTranscript -> checkerAgreement ->
    AyMCBRCheckerTranscript
      checkerAccepted checkerTranscript checkerAgreement :=
  fun haccepted htranscript hagree =>
    ay_mcbr_conj_intro haccepted (ay_mcbr_conj_intro htranscript hagree)

theorem ay_mcbr_formula_fingerprint_intro
    {originalFingerprint bundleFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> bundleFingerprint -> fingerprintAgreement ->
    AyMCBRFormulaFingerprint
      originalFingerprint bundleFingerprint fingerprintAgreement :=
  fun horiginal hbundle hagree =>
    ay_mcbr_conj_intro horiginal (ay_mcbr_conj_intro hbundle hagree)

theorem ay_mcbr_build_evidence_intro
    {solverBuild bundleBuild buildAgreement : Prop} :
    solverBuild -> bundleBuild -> buildAgreement ->
    AyMCBRBuildEvidence solverBuild bundleBuild buildAgreement :=
  fun hsolver hbundle hagree =>
    ay_mcbr_conj_intro hsolver (ay_mcbr_conj_intro hbundle hagree)

theorem ay_mcbr_roundtrip_evidence_intro
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    chunksOk -> digestOk -> mapsOk -> clauseReplayOk -> checkerOk ->
    fingerprintOk -> buildOk ->
    AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
      checkerOk fingerprintOk buildOk :=
  fun hchunks hdigest hmaps hclause hchecker hfingerprint hbuild =>
    ay_mcbr_conj_intro hchunks
      (ay_mcbr_conj_intro hdigest
        (ay_mcbr_conj_intro hmaps
          (ay_mcbr_conj_intro hclause
            (ay_mcbr_conj_intro hchecker
              (ay_mcbr_conj_intro hfingerprint hbuild)))))

theorem ay_mcbr_roundtrip_evidence_chunks
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    chunksOk :=
  fun h => ay_mcbr_conj_left h

theorem ay_mcbr_roundtrip_evidence_digest
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    digestOk :=
  fun h => ay_mcbr_conj_left (ay_mcbr_conj_right h)

theorem ay_mcbr_roundtrip_evidence_maps
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    mapsOk :=
  fun h => ay_mcbr_conj_left (ay_mcbr_conj_right (ay_mcbr_conj_right h))

theorem ay_mcbr_roundtrip_evidence_clause_replay
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    clauseReplayOk :=
  fun h =>
    ay_mcbr_conj_left
      (ay_mcbr_conj_right (ay_mcbr_conj_right (ay_mcbr_conj_right h)))

theorem ay_mcbr_roundtrip_evidence_checker
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    checkerOk :=
  fun h =>
    ay_mcbr_conj_left
      (ay_mcbr_conj_right
        (ay_mcbr_conj_right (ay_mcbr_conj_right (ay_mcbr_conj_right h))))

theorem ay_mcbr_roundtrip_evidence_fingerprint
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    fingerprintOk :=
  fun h =>
    ay_mcbr_conj_left
      (ay_mcbr_conj_right
        (ay_mcbr_conj_right
          (ay_mcbr_conj_right (ay_mcbr_conj_right (ay_mcbr_conj_right h)))))

theorem ay_mcbr_roundtrip_evidence_build
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk
      buildOk : Prop} :
    AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    buildOk :=
  fun h =>
    ay_mcbr_conj_right
      (ay_mcbr_conj_right
        (ay_mcbr_conj_right
          (ay_mcbr_conj_right (ay_mcbr_conj_right (ay_mcbr_conj_right h)))))

theorem ay_mcbr_public_sat_witness_intro
    {roundtripEvidence publicWitness publicSatClaim : Prop} :
    roundtripEvidence -> publicWitness -> publicSatClaim ->
    AyMCBRPublicSatWitness roundtripEvidence publicWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mcbr_conj_intro hevidence (ay_mcbr_conj_intro hwitness hclaim)

theorem ay_mcbr_public_sat_witness_evidence
    {roundtripEvidence publicWitness publicSatClaim : Prop} :
    AyMCBRPublicSatWitness roundtripEvidence publicWitness publicSatClaim ->
    roundtripEvidence :=
  fun h => ay_mcbr_conj_left h

theorem ay_mcbr_public_sat_witness_claim
    {roundtripEvidence publicWitness publicSatClaim : Prop} :
    AyMCBRPublicSatWitness roundtripEvidence publicWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mcbr_conj_right (ay_mcbr_conj_right h)

theorem ay_mcbr_accepted_bundle_roundtrip_publishes_sound_sat
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
      checkerOk fingerprintOk buildOk ->
    publicWitness -> publicSatClaim ->
    AyMCBRPublicSatWitness
      (AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim :=
  ay_mcbr_public_sat_witness_intro

theorem ay_mcbr_public_sat_requires_roundtrip_evidence
    {roundtripEvidence publicWitness publicSatClaim : Prop} :
    AyMCBRPublicSatWitness roundtripEvidence publicWitness publicSatClaim ->
    roundtripEvidence :=
  ay_mcbr_public_sat_witness_evidence

theorem ay_mcbr_bundle_roundtrip_preserves_truth
    {bundleTruth publicTruth : Prop} :
    AyMCBREquisat bundleTruth publicTruth -> bundleTruth -> publicTruth :=
  ay_mcbr_equisat_forward

theorem ay_mcbr_publication_requires_chunks
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMCBRPublicSatWitness
      (AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    chunksOk :=
  fun h =>
    ay_mcbr_roundtrip_evidence_chunks
      (ay_mcbr_public_sat_witness_evidence h)

theorem ay_mcbr_publication_requires_digest
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMCBRPublicSatWitness
      (AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mcbr_roundtrip_evidence_digest
      (ay_mcbr_public_sat_witness_evidence h)

theorem ay_mcbr_publication_requires_maps
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMCBRPublicSatWitness
      (AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    mapsOk :=
  fun h =>
    ay_mcbr_roundtrip_evidence_maps
      (ay_mcbr_public_sat_witness_evidence h)

theorem ay_mcbr_publication_requires_clause_replay
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMCBRPublicSatWitness
      (AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_mcbr_roundtrip_evidence_clause_replay
      (ay_mcbr_public_sat_witness_evidence h)

theorem ay_mcbr_publication_requires_checker
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMCBRPublicSatWitness
      (AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    checkerOk :=
  fun h =>
    ay_mcbr_roundtrip_evidence_checker
      (ay_mcbr_public_sat_witness_evidence h)

theorem ay_mcbr_publication_requires_fingerprint
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMCBRPublicSatWitness
      (AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mcbr_roundtrip_evidence_fingerprint
      (ay_mcbr_public_sat_witness_evidence h)

theorem ay_mcbr_publication_requires_build
    {chunksOk digestOk mapsOk clauseReplayOk checkerOk fingerprintOk buildOk
      publicWitness publicSatClaim : Prop} :
    AyMCBRPublicSatWitness
      (AyMCBRRoundtripEvidence chunksOk digestOk mapsOk clauseReplayOk
        checkerOk fingerprintOk buildOk)
      publicWitness publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mcbr_roundtrip_evidence_build
      (ay_mcbr_public_sat_witness_evidence h)

theorem ay_mcbr_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyMCBRNoClaimDiagnostic reason blocksPublication :=
  ay_mcbr_conj_intro

theorem ay_mcbr_no_claim_diagnostic_reason
    {reason blocksPublication : Prop} :
    AyMCBRNoClaimDiagnostic reason blocksPublication -> reason :=
  ay_mcbr_conj_left

theorem ay_mcbr_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyMCBRNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_mcbr_conj_right

theorem ay_mcbr_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyMCBRRecomputeObligation reason recomputeRequested :=
  ay_mcbr_conj_intro

theorem ay_mcbr_recompute_obligation_reason
    {reason recomputeRequested : Prop} :
    AyMCBRRecomputeObligation reason recomputeRequested -> reason :=
  ay_mcbr_conj_left

theorem ay_mcbr_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyMCBRRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_mcbr_conj_right

theorem ay_mcbr_schema_drift_no_claim
    {schemaDrift blocksPublication : Prop} :
    schemaDrift -> blocksPublication ->
    AyMCBRNoClaimDiagnostic schemaDrift blocksPublication :=
  ay_mcbr_no_claim_diagnostic_intro

theorem ay_mcbr_schema_drift_recompute
    {schemaDrift recomputeRequested : Prop} :
    schemaDrift -> recomputeRequested ->
    AyMCBRRecomputeObligation schemaDrift recomputeRequested :=
  ay_mcbr_recompute_obligation_intro

theorem ay_mcbr_missing_chunk_no_claim
    {missingChunk blocksPublication : Prop} :
    missingChunk -> blocksPublication ->
    AyMCBRNoClaimDiagnostic missingChunk blocksPublication :=
  ay_mcbr_no_claim_diagnostic_intro

theorem ay_mcbr_missing_chunk_recompute
    {missingChunk recomputeRequested : Prop} :
    missingChunk -> recomputeRequested ->
    AyMCBRRecomputeObligation missingChunk recomputeRequested :=
  ay_mcbr_recompute_obligation_intro

theorem ay_mcbr_digest_mismatch_no_claim
    {digestMismatch blocksPublication : Prop} :
    digestMismatch -> blocksPublication ->
    AyMCBRNoClaimDiagnostic digestMismatch blocksPublication :=
  ay_mcbr_no_claim_diagnostic_intro

theorem ay_mcbr_map_mismatch_no_claim
    {mapMismatch blocksPublication : Prop} :
    mapMismatch -> blocksPublication ->
    AyMCBRNoClaimDiagnostic mapMismatch blocksPublication :=
  ay_mcbr_no_claim_diagnostic_intro

theorem ay_mcbr_stale_fingerprint_no_claim
    {staleFingerprint blocksPublication : Prop} :
    staleFingerprint -> blocksPublication ->
    AyMCBRNoClaimDiagnostic staleFingerprint blocksPublication :=
  ay_mcbr_no_claim_diagnostic_intro

theorem ay_mcbr_checker_rejection_no_claim
    {checkerRejected blocksPublication : Prop} :
    checkerRejected -> blocksPublication ->
    AyMCBRNoClaimDiagnostic checkerRejected blocksPublication :=
  ay_mcbr_no_claim_diagnostic_intro

theorem ay_mcbr_diagnostic_blocks_publication
    {reason blocksPublication : Prop} :
    AyMCBRNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_mcbr_no_claim_diagnostic_blocks

theorem ay_mcbr_bad_bundle_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyMCBRNoClaimDiagnostic failure blocksPublication ->
    AyMCBRRecomputeObligation failure recomputeRequested ->
    AyMCBRConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_mcbr_conj_intro
      (ay_mcbr_no_claim_diagnostic_blocks hdiagnostic)
      (ay_mcbr_recompute_obligation_request hrecompute)
