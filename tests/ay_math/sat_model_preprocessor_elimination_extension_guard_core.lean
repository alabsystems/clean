/- SAT-COMP/ay preprocessing elimination-extension model guard.

This self-contained package models sequential-main SAT publication after
preprocessing eliminates variables.  Projection is accepted only when the
elimination manifest, extension map, witness ledger, reduced/original digests,
replay, checker, fingerprint, build, and archive evidence all agree.
-/

def AyPEEGConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyPEEGDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyPEEGEquisat (source target : Prop) : Prop :=
  AyPEEGConj (source -> target) (target -> source)

def AyPEEGEliminationManifest
    (originalVariables eliminatedVariables eliminationAgreement : Prop) : Prop :=
  AyPEEGConj originalVariables
    (AyPEEGConj eliminatedVariables eliminationAgreement)

def AyPEEGExtensionMap
    (reducedToOriginal originalToReduced mapAgreement : Prop) : Prop :=
  AyPEEGConj reducedToOriginal (AyPEEGConj originalToReduced mapAgreement)

def AyPEEGExtensionWitnessLedger
    (extensionWitness witnessLedger witnessAgreement : Prop) : Prop :=
  AyPEEGConj extensionWitness (AyPEEGConj witnessLedger witnessAgreement)

def AyPEEGOriginalAssignmentDigest
    (originalAssignment originalDigest originalDigestAgreement : Prop) : Prop :=
  AyPEEGConj originalAssignment
    (AyPEEGConj originalDigest originalDigestAgreement)

def AyPEEGReducedAssignmentDigest
    (reducedAssignment reducedDigest reducedDigestAgreement : Prop) : Prop :=
  AyPEEGConj reducedAssignment
    (AyPEEGConj reducedDigest reducedDigestAgreement)

def AyPEEGClauseReplay
    (clauseReplay originalEvaluation replayAgreement : Prop) : Prop :=
  AyPEEGConj clauseReplay (AyPEEGConj originalEvaluation replayAgreement)

def AyPEEGCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyPEEGConj checkerAccepted (AyPEEGConj transcript transcriptAgreement)

def AyPEEGFormulaFingerprint
    (originalFingerprint reducedFingerprint fingerprintAgreement : Prop) : Prop :=
  AyPEEGConj originalFingerprint
    (AyPEEGConj reducedFingerprint fingerprintAgreement)

def AyPEEGBuildEvidence
    (solverBuild preprocessingBuild buildAgreement : Prop) : Prop :=
  AyPEEGConj solverBuild (AyPEEGConj preprocessingBuild buildAgreement)

def AyPEEGArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AyPEEGConj archiveEntry (AyPEEGConj archiveDigest archiveAgreement)

def AyPEEGAcceptedProjection
    (eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AyPEEGConj eliminationOk
    (AyPEEGConj mapOk
      (AyPEEGConj witnessOk
        (AyPEEGConj originalDigestOk
          (AyPEEGConj reducedDigestOk
            (AyPEEGConj replayOk
              (AyPEEGConj checkerOk
                (AyPEEGConj fingerprintOk
                  (AyPEEGConj buildOk archiveOk))))))))

def AyPEEGPublicSatWitness
    (acceptedProjection originalWitness publicSatClaim : Prop) : Prop :=
  AyPEEGConj acceptedProjection (AyPEEGConj originalWitness publicSatClaim)

def AyPEEGNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyPEEGConj reason blocksPublication

def AyPEEGRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyPEEGConj reason recomputeRequested

theorem ay_peeg_conj_intro {left right : Prop} :
    left -> right -> AyPEEGConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_peeg_conj_left {left right : Prop} :
    AyPEEGConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_peeg_conj_right {left right : Prop} :
    AyPEEGConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_peeg_disj_left {left right : Prop} :
    left -> AyPEEGDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_peeg_disj_right {left right : Prop} :
    right -> AyPEEGDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_peeg_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyPEEGEquisat source target :=
  fun forward backward => ay_peeg_conj_intro forward backward

theorem ay_peeg_equisat_forward {source target : Prop} :
    AyPEEGEquisat source target -> source -> target :=
  fun h => ay_peeg_conj_left h

theorem ay_peeg_equisat_backward {source target : Prop} :
    AyPEEGEquisat source target -> target -> source :=
  fun h => ay_peeg_conj_right h

theorem ay_peeg_elimination_manifest_intro
    {originalVariables eliminatedVariables eliminationAgreement : Prop} :
    originalVariables -> eliminatedVariables -> eliminationAgreement ->
    AyPEEGEliminationManifest
      originalVariables eliminatedVariables eliminationAgreement :=
  fun horiginal heliminated hagree =>
    ay_peeg_conj_intro horiginal (ay_peeg_conj_intro heliminated hagree)

theorem ay_peeg_elimination_manifest_original
    {originalVariables eliminatedVariables eliminationAgreement : Prop} :
    AyPEEGEliminationManifest
      originalVariables eliminatedVariables eliminationAgreement ->
    originalVariables :=
  fun h => ay_peeg_conj_left h

theorem ay_peeg_elimination_manifest_eliminated
    {originalVariables eliminatedVariables eliminationAgreement : Prop} :
    AyPEEGEliminationManifest
      originalVariables eliminatedVariables eliminationAgreement ->
    eliminatedVariables :=
  fun h => ay_peeg_conj_left (ay_peeg_conj_right h)

theorem ay_peeg_elimination_manifest_agreement
    {originalVariables eliminatedVariables eliminationAgreement : Prop} :
    AyPEEGEliminationManifest
      originalVariables eliminatedVariables eliminationAgreement ->
    eliminationAgreement :=
  fun h => ay_peeg_conj_right (ay_peeg_conj_right h)

theorem ay_peeg_extension_map_intro
    {reducedToOriginal originalToReduced mapAgreement : Prop} :
    reducedToOriginal -> originalToReduced -> mapAgreement ->
    AyPEEGExtensionMap reducedToOriginal originalToReduced mapAgreement :=
  fun hforward hbackward hagree =>
    ay_peeg_conj_intro hforward (ay_peeg_conj_intro hbackward hagree)

theorem ay_peeg_extension_witness_ledger_intro
    {extensionWitness witnessLedger witnessAgreement : Prop} :
    extensionWitness -> witnessLedger -> witnessAgreement ->
    AyPEEGExtensionWitnessLedger
      extensionWitness witnessLedger witnessAgreement :=
  fun hwitness hledger hagree =>
    ay_peeg_conj_intro hwitness (ay_peeg_conj_intro hledger hagree)

theorem ay_peeg_original_assignment_digest_intro
    {originalAssignment originalDigest originalDigestAgreement : Prop} :
    originalAssignment -> originalDigest -> originalDigestAgreement ->
    AyPEEGOriginalAssignmentDigest
      originalAssignment originalDigest originalDigestAgreement :=
  fun hassignment hdigest hagree =>
    ay_peeg_conj_intro hassignment (ay_peeg_conj_intro hdigest hagree)

theorem ay_peeg_reduced_assignment_digest_intro
    {reducedAssignment reducedDigest reducedDigestAgreement : Prop} :
    reducedAssignment -> reducedDigest -> reducedDigestAgreement ->
    AyPEEGReducedAssignmentDigest
      reducedAssignment reducedDigest reducedDigestAgreement :=
  fun hassignment hdigest hagree =>
    ay_peeg_conj_intro hassignment (ay_peeg_conj_intro hdigest hagree)

theorem ay_peeg_clause_replay_intro
    {clauseReplay originalEvaluation replayAgreement : Prop} :
    clauseReplay -> originalEvaluation -> replayAgreement ->
    AyPEEGClauseReplay clauseReplay originalEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_peeg_conj_intro hreplay (ay_peeg_conj_intro heval hagree)

theorem ay_peeg_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyPEEGCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_peeg_conj_intro haccepted (ay_peeg_conj_intro htranscript hagree)

theorem ay_peeg_formula_fingerprint_intro
    {originalFingerprint reducedFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> reducedFingerprint -> fingerprintAgreement ->
    AyPEEGFormulaFingerprint
      originalFingerprint reducedFingerprint fingerprintAgreement :=
  fun horiginal hreduced hagree =>
    ay_peeg_conj_intro horiginal (ay_peeg_conj_intro hreduced hagree)

theorem ay_peeg_build_evidence_intro
    {solverBuild preprocessingBuild buildAgreement : Prop} :
    solverBuild -> preprocessingBuild -> buildAgreement ->
    AyPEEGBuildEvidence solverBuild preprocessingBuild buildAgreement :=
  fun hsolver hpreprocessing hagree =>
    ay_peeg_conj_intro hsolver (ay_peeg_conj_intro hpreprocessing hagree)

theorem ay_peeg_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AyPEEGArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_peeg_conj_intro hentry (ay_peeg_conj_intro hdigest hagree)

theorem ay_peeg_accepted_projection_intro
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    eliminationOk -> mapOk -> witnessOk -> originalDigestOk ->
    reducedDigestOk -> replayOk -> checkerOk -> fingerprintOk -> buildOk ->
    archiveOk ->
    AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
      reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk :=
  fun helimination hmap hwitness horiginalDigest hreducedDigest hreplay hchecker
      hfingerprint hbuild harchive =>
    ay_peeg_conj_intro helimination
      (ay_peeg_conj_intro hmap
        (ay_peeg_conj_intro hwitness
          (ay_peeg_conj_intro horiginalDigest
            (ay_peeg_conj_intro hreducedDigest
              (ay_peeg_conj_intro hreplay
                (ay_peeg_conj_intro hchecker
                  (ay_peeg_conj_intro hfingerprint
                    (ay_peeg_conj_intro hbuild harchive))))))))

theorem ay_peeg_accepted_projection_elimination
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
      reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    eliminationOk :=
  fun h => ay_peeg_conj_left h

theorem ay_peeg_accepted_projection_map
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
      reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    mapOk :=
  fun h => ay_peeg_conj_left (ay_peeg_conj_right h)

theorem ay_peeg_accepted_projection_witness
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
      reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    witnessOk :=
  fun h => ay_peeg_conj_left (ay_peeg_conj_right (ay_peeg_conj_right h))

theorem ay_peeg_accepted_projection_original_digest
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
      reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    originalDigestOk :=
  fun h =>
    ay_peeg_conj_left
      (ay_peeg_conj_right (ay_peeg_conj_right (ay_peeg_conj_right h)))

theorem ay_peeg_accepted_projection_reduced_digest
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
      reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    reducedDigestOk :=
  fun h =>
    ay_peeg_conj_left
      (ay_peeg_conj_right
        (ay_peeg_conj_right (ay_peeg_conj_right (ay_peeg_conj_right h))))

theorem ay_peeg_accepted_projection_replay
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
      reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    replayOk :=
  fun h =>
    ay_peeg_conj_left
      (ay_peeg_conj_right
        (ay_peeg_conj_right
          (ay_peeg_conj_right (ay_peeg_conj_right
            (ay_peeg_conj_right h)))))

theorem ay_peeg_accepted_projection_checker
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
      reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_peeg_conj_left
      (ay_peeg_conj_right
        (ay_peeg_conj_right
          (ay_peeg_conj_right
            (ay_peeg_conj_right (ay_peeg_conj_right
              (ay_peeg_conj_right h))))))

theorem ay_peeg_accepted_projection_fingerprint
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
      reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_peeg_conj_left
      (ay_peeg_conj_right
        (ay_peeg_conj_right
          (ay_peeg_conj_right
            (ay_peeg_conj_right
              (ay_peeg_conj_right (ay_peeg_conj_right
                (ay_peeg_conj_right h)))))))

theorem ay_peeg_accepted_projection_build
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
      reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_peeg_conj_left
      (ay_peeg_conj_right
        (ay_peeg_conj_right
          (ay_peeg_conj_right
            (ay_peeg_conj_right
              (ay_peeg_conj_right
                (ay_peeg_conj_right (ay_peeg_conj_right
                  (ay_peeg_conj_right h))))))))

theorem ay_peeg_accepted_projection_archive
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk : Prop} :
    AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
      reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_peeg_conj_right
      (ay_peeg_conj_right
        (ay_peeg_conj_right
          (ay_peeg_conj_right
            (ay_peeg_conj_right
              (ay_peeg_conj_right
                (ay_peeg_conj_right (ay_peeg_conj_right
                  (ay_peeg_conj_right h))))))))

theorem ay_peeg_public_sat_witness_intro
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    acceptedProjection -> originalWitness -> publicSatClaim ->
    AyPEEGPublicSatWitness acceptedProjection originalWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_peeg_conj_intro hevidence (ay_peeg_conj_intro hwitness hclaim)

theorem ay_peeg_public_sat_witness_evidence
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyPEEGPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    acceptedProjection :=
  fun h => ay_peeg_conj_left h

theorem ay_peeg_public_sat_witness_claim
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyPEEGPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_peeg_conj_right (ay_peeg_conj_right h)

theorem ay_peeg_accepted_projection_publishes_sound_sat
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk originalWitness
      publicSatClaim : Prop} :
    AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
      reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    originalWitness -> publicSatClaim ->
    AyPEEGPublicSatWitness
      (AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
        reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim :=
  ay_peeg_public_sat_witness_intro

theorem ay_peeg_projection_reconstructs_original_assignment
    {reducedTruth originalTruth : Prop} :
    AyPEEGEquisat reducedTruth originalTruth -> reducedTruth -> originalTruth :=
  ay_peeg_equisat_forward

theorem ay_peeg_public_sat_requires_accepted_projection
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AyPEEGPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    acceptedProjection :=
  ay_peeg_public_sat_witness_evidence

theorem ay_peeg_publication_requires_elimination
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk originalWitness
      publicSatClaim : Prop} :
    AyPEEGPublicSatWitness
      (AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
        reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    eliminationOk :=
  fun h => ay_peeg_accepted_projection_elimination
    (ay_peeg_public_sat_witness_evidence h)

theorem ay_peeg_publication_requires_map
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk originalWitness
      publicSatClaim : Prop} :
    AyPEEGPublicSatWitness
      (AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
        reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    mapOk :=
  fun h => ay_peeg_accepted_projection_map
    (ay_peeg_public_sat_witness_evidence h)

theorem ay_peeg_publication_requires_witness
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk originalWitness
      publicSatClaim : Prop} :
    AyPEEGPublicSatWitness
      (AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
        reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    witnessOk :=
  fun h => ay_peeg_accepted_projection_witness
    (ay_peeg_public_sat_witness_evidence h)

theorem ay_peeg_publication_requires_original_digest
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk originalWitness
      publicSatClaim : Prop} :
    AyPEEGPublicSatWitness
      (AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
        reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    originalDigestOk :=
  fun h => ay_peeg_accepted_projection_original_digest
    (ay_peeg_public_sat_witness_evidence h)

theorem ay_peeg_publication_requires_reduced_digest
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk originalWitness
      publicSatClaim : Prop} :
    AyPEEGPublicSatWitness
      (AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
        reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    reducedDigestOk :=
  fun h => ay_peeg_accepted_projection_reduced_digest
    (ay_peeg_public_sat_witness_evidence h)

theorem ay_peeg_publication_requires_replay
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk originalWitness
      publicSatClaim : Prop} :
    AyPEEGPublicSatWitness
      (AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
        reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    replayOk :=
  fun h => ay_peeg_accepted_projection_replay
    (ay_peeg_public_sat_witness_evidence h)

theorem ay_peeg_publication_requires_checker
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk originalWitness
      publicSatClaim : Prop} :
    AyPEEGPublicSatWitness
      (AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
        reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_peeg_accepted_projection_checker
    (ay_peeg_public_sat_witness_evidence h)

theorem ay_peeg_publication_requires_fingerprint
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk originalWitness
      publicSatClaim : Prop} :
    AyPEEGPublicSatWitness
      (AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
        reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_peeg_accepted_projection_fingerprint
    (ay_peeg_public_sat_witness_evidence h)

theorem ay_peeg_publication_requires_build
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk originalWitness
      publicSatClaim : Prop} :
    AyPEEGPublicSatWitness
      (AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
        reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    buildOk :=
  fun h => ay_peeg_accepted_projection_build
    (ay_peeg_public_sat_witness_evidence h)

theorem ay_peeg_publication_requires_archive
    {eliminationOk mapOk witnessOk originalDigestOk reducedDigestOk replayOk
      checkerOk fingerprintOk buildOk archiveOk originalWitness
      publicSatClaim : Prop} :
    AyPEEGPublicSatWitness
      (AyPEEGAcceptedProjection eliminationOk mapOk witnessOk originalDigestOk
        reducedDigestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_peeg_accepted_projection_archive
    (ay_peeg_public_sat_witness_evidence h)

theorem ay_peeg_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyPEEGNoClaimDiagnostic reason blocksPublication :=
  ay_peeg_conj_intro

theorem ay_peeg_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyPEEGNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_peeg_conj_right

theorem ay_peeg_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyPEEGRecomputeObligation reason recomputeRequested :=
  ay_peeg_conj_intro

theorem ay_peeg_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyPEEGRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_peeg_conj_right

theorem ay_peeg_mismatch_no_claim
    {mismatch blocksPublication : Prop} :
    mismatch -> blocksPublication ->
    AyPEEGNoClaimDiagnostic mismatch blocksPublication :=
  ay_peeg_no_claim_diagnostic_intro

theorem ay_peeg_mismatch_recompute
    {mismatch recomputeRequested : Prop} :
    mismatch -> recomputeRequested ->
    AyPEEGRecomputeObligation mismatch recomputeRequested :=
  ay_peeg_recompute_obligation_intro

theorem ay_peeg_elimination_mismatch_no_claim
    {eliminationMismatch blocksPublication : Prop} :
    eliminationMismatch -> blocksPublication ->
    AyPEEGNoClaimDiagnostic eliminationMismatch blocksPublication :=
  ay_peeg_mismatch_no_claim

theorem ay_peeg_map_mismatch_no_claim
    {mapMismatch blocksPublication : Prop} :
    mapMismatch -> blocksPublication ->
    AyPEEGNoClaimDiagnostic mapMismatch blocksPublication :=
  ay_peeg_mismatch_no_claim

theorem ay_peeg_witness_mismatch_no_claim
    {witnessMismatch blocksPublication : Prop} :
    witnessMismatch -> blocksPublication ->
    AyPEEGNoClaimDiagnostic witnessMismatch blocksPublication :=
  ay_peeg_mismatch_no_claim

theorem ay_peeg_digest_mismatch_no_claim
    {digestMismatch blocksPublication : Prop} :
    digestMismatch -> blocksPublication ->
    AyPEEGNoClaimDiagnostic digestMismatch blocksPublication :=
  ay_peeg_mismatch_no_claim

theorem ay_peeg_replay_mismatch_no_claim
    {replayMismatch blocksPublication : Prop} :
    replayMismatch -> blocksPublication ->
    AyPEEGNoClaimDiagnostic replayMismatch blocksPublication :=
  ay_peeg_mismatch_no_claim

theorem ay_peeg_checker_mismatch_no_claim
    {checkerMismatch blocksPublication : Prop} :
    checkerMismatch -> blocksPublication ->
    AyPEEGNoClaimDiagnostic checkerMismatch blocksPublication :=
  ay_peeg_mismatch_no_claim

theorem ay_peeg_fingerprint_mismatch_no_claim
    {fingerprintMismatch blocksPublication : Prop} :
    fingerprintMismatch -> blocksPublication ->
    AyPEEGNoClaimDiagnostic fingerprintMismatch blocksPublication :=
  ay_peeg_mismatch_no_claim

theorem ay_peeg_build_mismatch_no_claim
    {buildMismatch blocksPublication : Prop} :
    buildMismatch -> blocksPublication ->
    AyPEEGNoClaimDiagnostic buildMismatch blocksPublication :=
  ay_peeg_mismatch_no_claim

theorem ay_peeg_archive_mismatch_no_claim
    {archiveMismatch blocksPublication : Prop} :
    archiveMismatch -> blocksPublication ->
    AyPEEGNoClaimDiagnostic archiveMismatch blocksPublication :=
  ay_peeg_mismatch_no_claim

theorem ay_peeg_failed_projection_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyPEEGNoClaimDiagnostic failure blocksPublication ->
    AyPEEGRecomputeObligation failure recomputeRequested ->
    AyPEEGConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_peeg_conj_intro
      (ay_peeg_no_claim_diagnostic_blocks hdiagnostic)
      (ay_peeg_recompute_obligation_request hrecompute)
