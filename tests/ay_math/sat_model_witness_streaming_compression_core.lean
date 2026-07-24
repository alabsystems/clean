/- SAT-COMP/ay model witness streaming-compression contract.

This file is intentionally self-contained and propositional.  The predicates
record the evidence gates that a sequential-main SAT witness stream must pass
before ay may publish a public SAT result.
-/

def AyMWSCConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMWSCDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMWSCEquisat (source target : Prop) : Prop :=
  AyMWSCConj (source -> target) (target -> source)

def AyMWSCChunkManifest
    (streamManifest chunkManifest chunkAgreement : Prop) : Prop :=
  AyMWSCConj streamManifest (AyMWSCConj chunkManifest chunkAgreement)

def AyMWSCDecompressionTranscript
    (compressedStream decompressedWitness decompressionAgreement : Prop) : Prop :=
  AyMWSCConj compressedStream
    (AyMWSCConj decompressedWitness decompressionAgreement)

def AyMWSCAssignmentDigest
    (compressedDigest witnessDigest digestAgreement : Prop) : Prop :=
  AyMWSCConj compressedDigest (AyMWSCConj witnessDigest digestAgreement)

def AyMWSCDimacsVariableMaps
    (streamVariableMap dimacsVariableMap mapAgreement : Prop) : Prop :=
  AyMWSCConj streamVariableMap (AyMWSCConj dimacsVariableMap mapAgreement)

def AyMWSCClauseReplay
    (clauseReplay witnessEvaluation evaluationAgreement : Prop) : Prop :=
  AyMWSCConj clauseReplay (AyMWSCConj witnessEvaluation evaluationAgreement)

def AyMWSCCheckerTranscript
    (checkerAccepted transcript replayAgreement : Prop) : Prop :=
  AyMWSCConj checkerAccepted (AyMWSCConj transcript replayAgreement)

def AyMWSCFormulaFingerprint
    (originalFingerprint streamFingerprint fingerprintAgreement : Prop) : Prop :=
  AyMWSCConj originalFingerprint
    (AyMWSCConj streamFingerprint fingerprintAgreement)

def AyMWSCBuildEvidence
    (solverBuild streamBuild buildAgreement : Prop) : Prop :=
  AyMWSCConj solverBuild (AyMWSCConj streamBuild buildAgreement)

def AyMWSCAcceptedEvidence
    (chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop) : Prop :=
  AyMWSCConj chunksOk
    (AyMWSCConj decompressionOk
      (AyMWSCConj digestOk
        (AyMWSCConj mapsOk
          (AyMWSCConj clauseReplayOk
            (AyMWSCConj transcriptOk
              (AyMWSCConj fingerprintOk buildOk))))))

def AyMWSCPublicSatWitness
    (acceptedEvidence streamedWitness publicSatClaim : Prop) : Prop :=
  AyMWSCConj acceptedEvidence
    (AyMWSCConj streamedWitness publicSatClaim)

def AyMWSCNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyMWSCConj reason blocksPublication

def AyMWSCRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyMWSCConj reason recomputeRequested

theorem ay_mwsc_conj_intro {left right : Prop} :
    left -> right -> AyMWSCConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mwsc_conj_left {left right : Prop} :
    AyMWSCConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mwsc_conj_right {left right : Prop} :
    AyMWSCConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mwsc_disj_left {left right : Prop} :
    left -> AyMWSCDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mwsc_disj_right {left right : Prop} :
    right -> AyMWSCDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mwsc_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyMWSCEquisat source target :=
  fun forward backward =>
    ay_mwsc_conj_intro forward backward

theorem ay_mwsc_equisat_forward {source target : Prop} :
    AyMWSCEquisat source target -> source -> target :=
  fun h => ay_mwsc_conj_left h

theorem ay_mwsc_equisat_backward {source target : Prop} :
    AyMWSCEquisat source target -> target -> source :=
  fun h => ay_mwsc_conj_right h

theorem ay_mwsc_chunk_manifest_intro
    {streamManifest chunkManifest chunkAgreement : Prop} :
    streamManifest -> chunkManifest -> chunkAgreement ->
    AyMWSCChunkManifest streamManifest chunkManifest chunkAgreement :=
  fun hstream hchunk hagree =>
    ay_mwsc_conj_intro hstream (ay_mwsc_conj_intro hchunk hagree)

theorem ay_mwsc_chunk_manifest_stream
    {streamManifest chunkManifest chunkAgreement : Prop} :
    AyMWSCChunkManifest streamManifest chunkManifest chunkAgreement ->
    streamManifest :=
  fun h => ay_mwsc_conj_left h

theorem ay_mwsc_chunk_manifest_chunks
    {streamManifest chunkManifest chunkAgreement : Prop} :
    AyMWSCChunkManifest streamManifest chunkManifest chunkAgreement ->
    chunkManifest :=
  fun h => ay_mwsc_conj_left (ay_mwsc_conj_right h)

theorem ay_mwsc_chunk_manifest_agreement
    {streamManifest chunkManifest chunkAgreement : Prop} :
    AyMWSCChunkManifest streamManifest chunkManifest chunkAgreement ->
    chunkAgreement :=
  fun h => ay_mwsc_conj_right (ay_mwsc_conj_right h)

theorem ay_mwsc_decompression_transcript_intro
    {compressedStream decompressedWitness decompressionAgreement : Prop} :
    compressedStream -> decompressedWitness -> decompressionAgreement ->
    AyMWSCDecompressionTranscript
      compressedStream decompressedWitness decompressionAgreement :=
  fun hstream hwitness hagree =>
    ay_mwsc_conj_intro hstream (ay_mwsc_conj_intro hwitness hagree)

theorem ay_mwsc_assignment_digest_intro
    {compressedDigest witnessDigest digestAgreement : Prop} :
    compressedDigest -> witnessDigest -> digestAgreement ->
    AyMWSCAssignmentDigest compressedDigest witnessDigest digestAgreement :=
  fun hcompressed hwitness hagree =>
    ay_mwsc_conj_intro hcompressed (ay_mwsc_conj_intro hwitness hagree)

theorem ay_mwsc_dimacs_variable_maps_intro
    {streamVariableMap dimacsVariableMap mapAgreement : Prop} :
    streamVariableMap -> dimacsVariableMap -> mapAgreement ->
    AyMWSCDimacsVariableMaps
      streamVariableMap dimacsVariableMap mapAgreement :=
  fun hstream hdimacs hagree =>
    ay_mwsc_conj_intro hstream (ay_mwsc_conj_intro hdimacs hagree)

theorem ay_mwsc_clause_replay_intro
    {clauseReplay witnessEvaluation evaluationAgreement : Prop} :
    clauseReplay -> witnessEvaluation -> evaluationAgreement ->
    AyMWSCClauseReplay clauseReplay witnessEvaluation evaluationAgreement :=
  fun hreplay heval hagree =>
    ay_mwsc_conj_intro hreplay (ay_mwsc_conj_intro heval hagree)

theorem ay_mwsc_checker_transcript_intro
    {checkerAccepted transcript replayAgreement : Prop} :
    checkerAccepted -> transcript -> replayAgreement ->
    AyMWSCCheckerTranscript checkerAccepted transcript replayAgreement :=
  fun haccepted htranscript hagree =>
    ay_mwsc_conj_intro haccepted (ay_mwsc_conj_intro htranscript hagree)

theorem ay_mwsc_formula_fingerprint_intro
    {originalFingerprint streamFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> streamFingerprint -> fingerprintAgreement ->
    AyMWSCFormulaFingerprint
      originalFingerprint streamFingerprint fingerprintAgreement :=
  fun horiginal hstream hagree =>
    ay_mwsc_conj_intro horiginal (ay_mwsc_conj_intro hstream hagree)

theorem ay_mwsc_build_evidence_intro
    {solverBuild streamBuild buildAgreement : Prop} :
    solverBuild -> streamBuild -> buildAgreement ->
    AyMWSCBuildEvidence solverBuild streamBuild buildAgreement :=
  fun hsolver hstream hagree =>
    ay_mwsc_conj_intro hsolver (ay_mwsc_conj_intro hstream hagree)

theorem ay_mwsc_accepted_evidence_intro
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    chunksOk -> decompressionOk -> digestOk -> mapsOk -> clauseReplayOk ->
    transcriptOk -> fingerprintOk -> buildOk ->
    AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
      clauseReplayOk transcriptOk fingerprintOk buildOk :=
  fun hchunks hdecomp hdigest hmaps hclause htranscript hfingerprint hbuild =>
    ay_mwsc_conj_intro hchunks
      (ay_mwsc_conj_intro hdecomp
        (ay_mwsc_conj_intro hdigest
          (ay_mwsc_conj_intro hmaps
            (ay_mwsc_conj_intro hclause
              (ay_mwsc_conj_intro htranscript
                (ay_mwsc_conj_intro hfingerprint hbuild))))))

theorem ay_mwsc_accepted_evidence_chunks
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
      clauseReplayOk transcriptOk fingerprintOk buildOk ->
    chunksOk :=
  fun h => ay_mwsc_conj_left h

theorem ay_mwsc_accepted_evidence_decompression
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
      clauseReplayOk transcriptOk fingerprintOk buildOk ->
    decompressionOk :=
  fun h => ay_mwsc_conj_left (ay_mwsc_conj_right h)

theorem ay_mwsc_accepted_evidence_digest
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
      clauseReplayOk transcriptOk fingerprintOk buildOk ->
    digestOk :=
  fun h => ay_mwsc_conj_left (ay_mwsc_conj_right (ay_mwsc_conj_right h))

theorem ay_mwsc_accepted_evidence_maps
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
      clauseReplayOk transcriptOk fingerprintOk buildOk ->
    mapsOk :=
  fun h =>
    ay_mwsc_conj_left
      (ay_mwsc_conj_right (ay_mwsc_conj_right (ay_mwsc_conj_right h)))

theorem ay_mwsc_accepted_evidence_clause_replay
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
      clauseReplayOk transcriptOk fingerprintOk buildOk ->
    clauseReplayOk :=
  fun h =>
    ay_mwsc_conj_left
      (ay_mwsc_conj_right
        (ay_mwsc_conj_right (ay_mwsc_conj_right (ay_mwsc_conj_right h))))

theorem ay_mwsc_accepted_evidence_transcript
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
      clauseReplayOk transcriptOk fingerprintOk buildOk ->
    transcriptOk :=
  fun h =>
    ay_mwsc_conj_left
      (ay_mwsc_conj_right
        (ay_mwsc_conj_right
          (ay_mwsc_conj_right (ay_mwsc_conj_right (ay_mwsc_conj_right h)))))

theorem ay_mwsc_accepted_evidence_fingerprint
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
      clauseReplayOk transcriptOk fingerprintOk buildOk ->
    fingerprintOk :=
  fun h =>
    ay_mwsc_conj_left
      (ay_mwsc_conj_right
        (ay_mwsc_conj_right
          (ay_mwsc_conj_right
            (ay_mwsc_conj_right (ay_mwsc_conj_right
              (ay_mwsc_conj_right h))))))

theorem ay_mwsc_accepted_evidence_build
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk : Prop} :
    AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
      clauseReplayOk transcriptOk fingerprintOk buildOk ->
    buildOk :=
  fun h =>
    ay_mwsc_conj_right
      (ay_mwsc_conj_right
        (ay_mwsc_conj_right
          (ay_mwsc_conj_right
            (ay_mwsc_conj_right (ay_mwsc_conj_right
              (ay_mwsc_conj_right h))))))

theorem ay_mwsc_public_sat_witness_intro
    {acceptedEvidence streamedWitness publicSatClaim : Prop} :
    acceptedEvidence -> streamedWitness -> publicSatClaim ->
    AyMWSCPublicSatWitness acceptedEvidence streamedWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_mwsc_conj_intro hevidence (ay_mwsc_conj_intro hwitness hclaim)

theorem ay_mwsc_public_sat_witness_evidence
    {acceptedEvidence streamedWitness publicSatClaim : Prop} :
    AyMWSCPublicSatWitness acceptedEvidence streamedWitness publicSatClaim ->
    acceptedEvidence :=
  fun h => ay_mwsc_conj_left h

theorem ay_mwsc_public_sat_witness_stream
    {acceptedEvidence streamedWitness publicSatClaim : Prop} :
    AyMWSCPublicSatWitness acceptedEvidence streamedWitness publicSatClaim ->
    streamedWitness :=
  fun h => ay_mwsc_conj_left (ay_mwsc_conj_right h)

theorem ay_mwsc_public_sat_witness_claim
    {acceptedEvidence streamedWitness publicSatClaim : Prop} :
    AyMWSCPublicSatWitness acceptedEvidence streamedWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_mwsc_conj_right (ay_mwsc_conj_right h)

theorem ay_mwsc_accepted_streaming_compression_publishes_sound_sat
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk streamedWitness publicSatClaim : Prop} :
    AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
      clauseReplayOk transcriptOk fingerprintOk buildOk ->
    streamedWitness -> publicSatClaim ->
    AyMWSCPublicSatWitness
      (AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
        clauseReplayOk transcriptOk fingerprintOk buildOk)
      streamedWitness publicSatClaim :=
  ay_mwsc_public_sat_witness_intro

theorem ay_mwsc_public_sat_requires_accepted_evidence
    {acceptedEvidence streamedWitness publicSatClaim : Prop} :
    AyMWSCPublicSatWitness acceptedEvidence streamedWitness publicSatClaim ->
    acceptedEvidence :=
  ay_mwsc_public_sat_witness_evidence

theorem ay_mwsc_publication_requires_chunks
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk streamedWitness publicSatClaim : Prop} :
    AyMWSCPublicSatWitness
      (AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
        clauseReplayOk transcriptOk fingerprintOk buildOk)
      streamedWitness publicSatClaim ->
    chunksOk :=
  fun h =>
    ay_mwsc_accepted_evidence_chunks
      (ay_mwsc_public_sat_witness_evidence h)

theorem ay_mwsc_publication_requires_decompression
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk streamedWitness publicSatClaim : Prop} :
    AyMWSCPublicSatWitness
      (AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
        clauseReplayOk transcriptOk fingerprintOk buildOk)
      streamedWitness publicSatClaim ->
    decompressionOk :=
  fun h =>
    ay_mwsc_accepted_evidence_decompression
      (ay_mwsc_public_sat_witness_evidence h)

theorem ay_mwsc_publication_requires_digest
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk streamedWitness publicSatClaim : Prop} :
    AyMWSCPublicSatWitness
      (AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
        clauseReplayOk transcriptOk fingerprintOk buildOk)
      streamedWitness publicSatClaim ->
    digestOk :=
  fun h =>
    ay_mwsc_accepted_evidence_digest
      (ay_mwsc_public_sat_witness_evidence h)

theorem ay_mwsc_publication_requires_maps
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk streamedWitness publicSatClaim : Prop} :
    AyMWSCPublicSatWitness
      (AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
        clauseReplayOk transcriptOk fingerprintOk buildOk)
      streamedWitness publicSatClaim ->
    mapsOk :=
  fun h =>
    ay_mwsc_accepted_evidence_maps
      (ay_mwsc_public_sat_witness_evidence h)

theorem ay_mwsc_publication_requires_clause_replay
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk streamedWitness publicSatClaim : Prop} :
    AyMWSCPublicSatWitness
      (AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
        clauseReplayOk transcriptOk fingerprintOk buildOk)
      streamedWitness publicSatClaim ->
    clauseReplayOk :=
  fun h =>
    ay_mwsc_accepted_evidence_clause_replay
      (ay_mwsc_public_sat_witness_evidence h)

theorem ay_mwsc_publication_requires_transcript
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk streamedWitness publicSatClaim : Prop} :
    AyMWSCPublicSatWitness
      (AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
        clauseReplayOk transcriptOk fingerprintOk buildOk)
      streamedWitness publicSatClaim ->
    transcriptOk :=
  fun h =>
    ay_mwsc_accepted_evidence_transcript
      (ay_mwsc_public_sat_witness_evidence h)

theorem ay_mwsc_publication_requires_fingerprint
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk streamedWitness publicSatClaim : Prop} :
    AyMWSCPublicSatWitness
      (AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
        clauseReplayOk transcriptOk fingerprintOk buildOk)
      streamedWitness publicSatClaim ->
    fingerprintOk :=
  fun h =>
    ay_mwsc_accepted_evidence_fingerprint
      (ay_mwsc_public_sat_witness_evidence h)

theorem ay_mwsc_publication_requires_build
    {chunksOk decompressionOk digestOk mapsOk clauseReplayOk transcriptOk
      fingerprintOk buildOk streamedWitness publicSatClaim : Prop} :
    AyMWSCPublicSatWitness
      (AyMWSCAcceptedEvidence chunksOk decompressionOk digestOk mapsOk
        clauseReplayOk transcriptOk fingerprintOk buildOk)
      streamedWitness publicSatClaim ->
    buildOk :=
  fun h =>
    ay_mwsc_accepted_evidence_build
      (ay_mwsc_public_sat_witness_evidence h)

theorem ay_mwsc_decompression_preserves_truth
    {compressedTruth decompressedTruth : Prop} :
    AyMWSCEquisat compressedTruth decompressedTruth ->
    compressedTruth -> decompressedTruth :=
  ay_mwsc_equisat_forward

theorem ay_mwsc_clause_replay_transports_truth
    {streamTruth publicTruth : Prop} :
    AyMWSCEquisat streamTruth publicTruth -> streamTruth -> publicTruth :=
  ay_mwsc_equisat_forward

theorem ay_mwsc_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyMWSCNoClaimDiagnostic reason blocksPublication :=
  ay_mwsc_conj_intro

theorem ay_mwsc_no_claim_diagnostic_reason
    {reason blocksPublication : Prop} :
    AyMWSCNoClaimDiagnostic reason blocksPublication -> reason :=
  ay_mwsc_conj_left

theorem ay_mwsc_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyMWSCNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_mwsc_conj_right

theorem ay_mwsc_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyMWSCRecomputeObligation reason recomputeRequested :=
  ay_mwsc_conj_intro

theorem ay_mwsc_recompute_obligation_reason
    {reason recomputeRequested : Prop} :
    AyMWSCRecomputeObligation reason recomputeRequested -> reason :=
  ay_mwsc_conj_left

theorem ay_mwsc_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyMWSCRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_mwsc_conj_right

theorem ay_mwsc_decompression_drift_recompute
    {decompressionDrift recomputeRequested : Prop} :
    decompressionDrift -> recomputeRequested ->
    AyMWSCRecomputeObligation decompressionDrift recomputeRequested :=
  ay_mwsc_recompute_obligation_intro

theorem ay_mwsc_decompression_drift_no_claim
    {decompressionDrift blocksPublication : Prop} :
    decompressionDrift -> blocksPublication ->
    AyMWSCNoClaimDiagnostic decompressionDrift blocksPublication :=
  ay_mwsc_no_claim_diagnostic_intro

theorem ay_mwsc_missing_chunk_recompute
    {missingChunk recomputeRequested : Prop} :
    missingChunk -> recomputeRequested ->
    AyMWSCRecomputeObligation missingChunk recomputeRequested :=
  ay_mwsc_recompute_obligation_intro

theorem ay_mwsc_missing_chunk_no_claim
    {missingChunk blocksPublication : Prop} :
    missingChunk -> blocksPublication ->
    AyMWSCNoClaimDiagnostic missingChunk blocksPublication :=
  ay_mwsc_no_claim_diagnostic_intro

theorem ay_mwsc_digest_mismatch_no_claim
    {digestMismatch blocksPublication : Prop} :
    digestMismatch -> blocksPublication ->
    AyMWSCNoClaimDiagnostic digestMismatch blocksPublication :=
  ay_mwsc_no_claim_diagnostic_intro

theorem ay_mwsc_map_mismatch_no_claim
    {mapMismatch blocksPublication : Prop} :
    mapMismatch -> blocksPublication ->
    AyMWSCNoClaimDiagnostic mapMismatch blocksPublication :=
  ay_mwsc_no_claim_diagnostic_intro

theorem ay_mwsc_stale_fingerprint_no_claim
    {staleFingerprint blocksPublication : Prop} :
    staleFingerprint -> blocksPublication ->
    AyMWSCNoClaimDiagnostic staleFingerprint blocksPublication :=
  ay_mwsc_no_claim_diagnostic_intro

theorem ay_mwsc_checker_rejection_no_claim
    {checkerRejected blocksPublication : Prop} :
    checkerRejected -> blocksPublication ->
    AyMWSCNoClaimDiagnostic checkerRejected blocksPublication :=
  ay_mwsc_no_claim_diagnostic_intro

theorem ay_mwsc_diagnostic_blocks_public_claim
    {reason blocksPublication : Prop} :
    AyMWSCNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_mwsc_no_claim_diagnostic_blocks

theorem ay_mwsc_bad_streaming_compression_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyMWSCNoClaimDiagnostic failure blocksPublication ->
    AyMWSCRecomputeObligation failure recomputeRequested ->
    AyMWSCConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_mwsc_conj_intro
      (ay_mwsc_no_claim_diagnostic_blocks hdiagnostic)
      (ay_mwsc_recompute_obligation_request hrecompute)
