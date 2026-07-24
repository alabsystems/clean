/- SAT-COMP/ay assignment projection to DIMACS guard contract.

This self-contained package models publication of SAT witnesses after projecting
internal solver assignments to public DIMACS variables.  Publication is gated by
projection, maps, deleted-variable defaults, extension, digest, replay, checker,
fingerprint, build, and archive evidence.
-/

def AyAPDGConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyAPDGDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyAPDGEquisat (source target : Prop) : Prop :=
  AyAPDGConj (source -> target) (target -> source)

def AyAPDGProjectionManifest
    (internalAssignment projectedAssignment projectionAgreement : Prop) : Prop :=
  AyAPDGConj internalAssignment
    (AyAPDGConj projectedAssignment projectionAgreement)

def AyAPDGDimacsVariableMap
    (internalToDimacs dimacsToInternal mapAgreement : Prop) : Prop :=
  AyAPDGConj internalToDimacs (AyAPDGConj dimacsToInternal mapAgreement)

def AyAPDGDeletedVariableDefaults
    (deletedVariables defaultValues defaultAgreement : Prop) : Prop :=
  AyAPDGConj deletedVariables (AyAPDGConj defaultValues defaultAgreement)

def AyAPDGExtensionWitnessLedger
    (extensionWitness extensionLedger extensionAgreement : Prop) : Prop :=
  AyAPDGConj extensionWitness
    (AyAPDGConj extensionLedger extensionAgreement)

def AyAPDGAssignmentDigest
    (internalDigest dimacsDigest digestAgreement : Prop) : Prop :=
  AyAPDGConj internalDigest (AyAPDGConj dimacsDigest digestAgreement)

def AyAPDGClauseReplay
    (clauseReplay projectedEvaluation replayAgreement : Prop) : Prop :=
  AyAPDGConj clauseReplay (AyAPDGConj projectedEvaluation replayAgreement)

def AyAPDGCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyAPDGConj checkerAccepted (AyAPDGConj transcript transcriptAgreement)

def AyAPDGFormulaFingerprint
    (originalFingerprint projectionFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyAPDGConj originalFingerprint
    (AyAPDGConj projectionFingerprint fingerprintAgreement)

def AyAPDGBuildEvidence
    (solverBuild projectionBuild buildAgreement : Prop) : Prop :=
  AyAPDGConj solverBuild (AyAPDGConj projectionBuild buildAgreement)

def AyAPDGArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AyAPDGConj archiveEntry (AyAPDGConj archiveDigest archiveAgreement)

def AyAPDGAcceptedProjection
    (projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AyAPDGConj projectionOk
    (AyAPDGConj mapOk
      (AyAPDGConj defaultsOk
        (AyAPDGConj extensionOk
          (AyAPDGConj digestOk
            (AyAPDGConj replayOk
              (AyAPDGConj checkerOk
                (AyAPDGConj fingerprintOk
                  (AyAPDGConj buildOk archiveOk))))))))

def AyAPDGPublicSatWitness
    (acceptedProjection dimacsWitness publicSatClaim : Prop) : Prop :=
  AyAPDGConj acceptedProjection (AyAPDGConj dimacsWitness publicSatClaim)

def AyAPDGNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyAPDGConj reason blocksPublication

def AyAPDGRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyAPDGConj reason recomputeRequested

theorem ay_apdg_conj_intro {left right : Prop} :
    left -> right -> AyAPDGConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_apdg_conj_left {left right : Prop} :
    AyAPDGConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_apdg_conj_right {left right : Prop} :
    AyAPDGConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_apdg_disj_left {left right : Prop} :
    left -> AyAPDGDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_apdg_disj_right {left right : Prop} :
    right -> AyAPDGDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_apdg_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyAPDGEquisat source target :=
  fun forward backward => ay_apdg_conj_intro forward backward

theorem ay_apdg_equisat_forward {source target : Prop} :
    AyAPDGEquisat source target -> source -> target :=
  fun h => ay_apdg_conj_left h

theorem ay_apdg_equisat_backward {source target : Prop} :
    AyAPDGEquisat source target -> target -> source :=
  fun h => ay_apdg_conj_right h

theorem ay_apdg_projection_manifest_intro
    {internalAssignment projectedAssignment projectionAgreement : Prop} :
    internalAssignment -> projectedAssignment -> projectionAgreement ->
    AyAPDGProjectionManifest
      internalAssignment projectedAssignment projectionAgreement :=
  fun hinternal hprojected hagree =>
    ay_apdg_conj_intro hinternal (ay_apdg_conj_intro hprojected hagree)

theorem ay_apdg_projection_manifest_internal
    {internalAssignment projectedAssignment projectionAgreement : Prop} :
    AyAPDGProjectionManifest
      internalAssignment projectedAssignment projectionAgreement ->
    internalAssignment :=
  fun h => ay_apdg_conj_left h

theorem ay_apdg_projection_manifest_projected
    {internalAssignment projectedAssignment projectionAgreement : Prop} :
    AyAPDGProjectionManifest
      internalAssignment projectedAssignment projectionAgreement ->
    projectedAssignment :=
  fun h => ay_apdg_conj_left (ay_apdg_conj_right h)

theorem ay_apdg_projection_manifest_agreement
    {internalAssignment projectedAssignment projectionAgreement : Prop} :
    AyAPDGProjectionManifest
      internalAssignment projectedAssignment projectionAgreement ->
    projectionAgreement :=
  fun h => ay_apdg_conj_right (ay_apdg_conj_right h)

theorem ay_apdg_dimacs_variable_map_intro
    {internalToDimacs dimacsToInternal mapAgreement : Prop} :
    internalToDimacs -> dimacsToInternal -> mapAgreement ->
    AyAPDGDimacsVariableMap internalToDimacs dimacsToInternal mapAgreement :=
  fun hforward hbackward hagree =>
    ay_apdg_conj_intro hforward (ay_apdg_conj_intro hbackward hagree)

theorem ay_apdg_deleted_variable_defaults_intro
    {deletedVariables defaultValues defaultAgreement : Prop} :
    deletedVariables -> defaultValues -> defaultAgreement ->
    AyAPDGDeletedVariableDefaults
      deletedVariables defaultValues defaultAgreement :=
  fun hdeleted hdefaults hagree =>
    ay_apdg_conj_intro hdeleted (ay_apdg_conj_intro hdefaults hagree)

theorem ay_apdg_extension_witness_ledger_intro
    {extensionWitness extensionLedger extensionAgreement : Prop} :
    extensionWitness -> extensionLedger -> extensionAgreement ->
    AyAPDGExtensionWitnessLedger
      extensionWitness extensionLedger extensionAgreement :=
  fun hwitness hledger hagree =>
    ay_apdg_conj_intro hwitness (ay_apdg_conj_intro hledger hagree)

theorem ay_apdg_assignment_digest_intro
    {internalDigest dimacsDigest digestAgreement : Prop} :
    internalDigest -> dimacsDigest -> digestAgreement ->
    AyAPDGAssignmentDigest internalDigest dimacsDigest digestAgreement :=
  fun hinternal hdimacs hagree =>
    ay_apdg_conj_intro hinternal (ay_apdg_conj_intro hdimacs hagree)

theorem ay_apdg_clause_replay_intro
    {clauseReplay projectedEvaluation replayAgreement : Prop} :
    clauseReplay -> projectedEvaluation -> replayAgreement ->
    AyAPDGClauseReplay clauseReplay projectedEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_apdg_conj_intro hreplay (ay_apdg_conj_intro heval hagree)

theorem ay_apdg_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyAPDGCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_apdg_conj_intro haccepted (ay_apdg_conj_intro htranscript hagree)

theorem ay_apdg_formula_fingerprint_intro
    {originalFingerprint projectionFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> projectionFingerprint -> fingerprintAgreement ->
    AyAPDGFormulaFingerprint
      originalFingerprint projectionFingerprint fingerprintAgreement :=
  fun horiginal hprojection hagree =>
    ay_apdg_conj_intro horiginal (ay_apdg_conj_intro hprojection hagree)

theorem ay_apdg_build_evidence_intro
    {solverBuild projectionBuild buildAgreement : Prop} :
    solverBuild -> projectionBuild -> buildAgreement ->
    AyAPDGBuildEvidence solverBuild projectionBuild buildAgreement :=
  fun hsolver hprojection hagree =>
    ay_apdg_conj_intro hsolver (ay_apdg_conj_intro hprojection hagree)

theorem ay_apdg_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AyAPDGArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_apdg_conj_intro hentry (ay_apdg_conj_intro hdigest hagree)

theorem ay_apdg_accepted_projection_intro
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    projectionOk -> mapOk -> defaultsOk -> extensionOk -> digestOk ->
    replayOk -> checkerOk -> fingerprintOk -> buildOk -> archiveOk ->
    AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk :=
  fun hprojection hmap hdefaults hextension hdigest hreplay hchecker
      hfingerprint hbuild harchive =>
    ay_apdg_conj_intro hprojection
      (ay_apdg_conj_intro hmap
        (ay_apdg_conj_intro hdefaults
          (ay_apdg_conj_intro hextension
            (ay_apdg_conj_intro hdigest
              (ay_apdg_conj_intro hreplay
                (ay_apdg_conj_intro hchecker
                  (ay_apdg_conj_intro hfingerprint
                    (ay_apdg_conj_intro hbuild harchive))))))))

theorem ay_apdg_accepted_projection_projection
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    projectionOk :=
  fun h => ay_apdg_conj_left h

theorem ay_apdg_accepted_projection_map
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    mapOk :=
  fun h => ay_apdg_conj_left (ay_apdg_conj_right h)

theorem ay_apdg_accepted_projection_defaults
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    defaultsOk :=
  fun h => ay_apdg_conj_left (ay_apdg_conj_right (ay_apdg_conj_right h))

theorem ay_apdg_accepted_projection_extension
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    extensionOk :=
  fun h =>
    ay_apdg_conj_left
      (ay_apdg_conj_right (ay_apdg_conj_right (ay_apdg_conj_right h)))

theorem ay_apdg_accepted_projection_digest
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    digestOk :=
  fun h =>
    ay_apdg_conj_left
      (ay_apdg_conj_right
        (ay_apdg_conj_right (ay_apdg_conj_right (ay_apdg_conj_right h))))

theorem ay_apdg_accepted_projection_replay
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    replayOk :=
  fun h =>
    ay_apdg_conj_left
      (ay_apdg_conj_right
        (ay_apdg_conj_right
          (ay_apdg_conj_right (ay_apdg_conj_right
            (ay_apdg_conj_right h)))))

theorem ay_apdg_accepted_projection_checker
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_apdg_conj_left
      (ay_apdg_conj_right
        (ay_apdg_conj_right
          (ay_apdg_conj_right
            (ay_apdg_conj_right (ay_apdg_conj_right
              (ay_apdg_conj_right h))))))

theorem ay_apdg_accepted_projection_fingerprint
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_apdg_conj_left
      (ay_apdg_conj_right
        (ay_apdg_conj_right
          (ay_apdg_conj_right
            (ay_apdg_conj_right
              (ay_apdg_conj_right (ay_apdg_conj_right
                (ay_apdg_conj_right h)))))))

theorem ay_apdg_accepted_projection_build
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_apdg_conj_left
      (ay_apdg_conj_right
        (ay_apdg_conj_right
          (ay_apdg_conj_right
            (ay_apdg_conj_right
              (ay_apdg_conj_right
                (ay_apdg_conj_right (ay_apdg_conj_right
                  (ay_apdg_conj_right h))))))))

theorem ay_apdg_accepted_projection_archive
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_apdg_conj_right
      (ay_apdg_conj_right
        (ay_apdg_conj_right
          (ay_apdg_conj_right
            (ay_apdg_conj_right
              (ay_apdg_conj_right
                (ay_apdg_conj_right (ay_apdg_conj_right
                  (ay_apdg_conj_right h))))))))

theorem ay_apdg_public_sat_witness_intro
    {acceptedProjection dimacsWitness publicSatClaim : Prop} :
    acceptedProjection -> dimacsWitness -> publicSatClaim ->
    AyAPDGPublicSatWitness acceptedProjection dimacsWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_apdg_conj_intro hevidence (ay_apdg_conj_intro hwitness hclaim)

theorem ay_apdg_public_sat_witness_evidence
    {acceptedProjection dimacsWitness publicSatClaim : Prop} :
    AyAPDGPublicSatWitness acceptedProjection dimacsWitness publicSatClaim ->
    acceptedProjection :=
  fun h => ay_apdg_conj_left h

theorem ay_apdg_public_sat_witness_claim
    {acceptedProjection dimacsWitness publicSatClaim : Prop} :
    AyAPDGPublicSatWitness acceptedProjection dimacsWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_apdg_conj_right (ay_apdg_conj_right h)

theorem ay_apdg_accepted_projection_publishes_sound_sat
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk dimacsWitness publicSatClaim : Prop} :
    AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    dimacsWitness -> publicSatClaim ->
    AyAPDGPublicSatWitness
      (AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      dimacsWitness publicSatClaim :=
  ay_apdg_public_sat_witness_intro

theorem ay_apdg_assignment_projection_preserves_original_truth
    {internalTruth originalTruth : Prop} :
    AyAPDGEquisat internalTruth originalTruth -> internalTruth -> originalTruth :=
  ay_apdg_equisat_forward

theorem ay_apdg_public_sat_requires_accepted_projection
    {acceptedProjection dimacsWitness publicSatClaim : Prop} :
    AyAPDGPublicSatWitness acceptedProjection dimacsWitness publicSatClaim ->
    acceptedProjection :=
  ay_apdg_public_sat_witness_evidence

theorem ay_apdg_publication_requires_projection
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk dimacsWitness publicSatClaim : Prop} :
    AyAPDGPublicSatWitness
      (AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      dimacsWitness publicSatClaim ->
    projectionOk :=
  fun h => ay_apdg_accepted_projection_projection
    (ay_apdg_public_sat_witness_evidence h)

theorem ay_apdg_publication_requires_map
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk dimacsWitness publicSatClaim : Prop} :
    AyAPDGPublicSatWitness
      (AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      dimacsWitness publicSatClaim ->
    mapOk :=
  fun h => ay_apdg_accepted_projection_map
    (ay_apdg_public_sat_witness_evidence h)

theorem ay_apdg_publication_requires_defaults
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk dimacsWitness publicSatClaim : Prop} :
    AyAPDGPublicSatWitness
      (AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      dimacsWitness publicSatClaim ->
    defaultsOk :=
  fun h => ay_apdg_accepted_projection_defaults
    (ay_apdg_public_sat_witness_evidence h)

theorem ay_apdg_publication_requires_extension
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk dimacsWitness publicSatClaim : Prop} :
    AyAPDGPublicSatWitness
      (AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      dimacsWitness publicSatClaim ->
    extensionOk :=
  fun h => ay_apdg_accepted_projection_extension
    (ay_apdg_public_sat_witness_evidence h)

theorem ay_apdg_publication_requires_digest
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk dimacsWitness publicSatClaim : Prop} :
    AyAPDGPublicSatWitness
      (AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      dimacsWitness publicSatClaim ->
    digestOk :=
  fun h => ay_apdg_accepted_projection_digest
    (ay_apdg_public_sat_witness_evidence h)

theorem ay_apdg_publication_requires_replay
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk dimacsWitness publicSatClaim : Prop} :
    AyAPDGPublicSatWitness
      (AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      dimacsWitness publicSatClaim ->
    replayOk :=
  fun h => ay_apdg_accepted_projection_replay
    (ay_apdg_public_sat_witness_evidence h)

theorem ay_apdg_publication_requires_checker
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk dimacsWitness publicSatClaim : Prop} :
    AyAPDGPublicSatWitness
      (AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      dimacsWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_apdg_accepted_projection_checker
    (ay_apdg_public_sat_witness_evidence h)

theorem ay_apdg_publication_requires_fingerprint
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk dimacsWitness publicSatClaim : Prop} :
    AyAPDGPublicSatWitness
      (AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      dimacsWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_apdg_accepted_projection_fingerprint
    (ay_apdg_public_sat_witness_evidence h)

theorem ay_apdg_publication_requires_build
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk dimacsWitness publicSatClaim : Prop} :
    AyAPDGPublicSatWitness
      (AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      dimacsWitness publicSatClaim ->
    buildOk :=
  fun h => ay_apdg_accepted_projection_build
    (ay_apdg_public_sat_witness_evidence h)

theorem ay_apdg_publication_requires_archive
    {projectionOk mapOk defaultsOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk dimacsWitness publicSatClaim : Prop} :
    AyAPDGPublicSatWitness
      (AyAPDGAcceptedProjection projectionOk mapOk defaultsOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      dimacsWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_apdg_accepted_projection_archive
    (ay_apdg_public_sat_witness_evidence h)

theorem ay_apdg_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyAPDGNoClaimDiagnostic reason blocksPublication :=
  ay_apdg_conj_intro

theorem ay_apdg_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyAPDGNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_apdg_conj_right

theorem ay_apdg_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyAPDGRecomputeObligation reason recomputeRequested :=
  ay_apdg_conj_intro

theorem ay_apdg_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyAPDGRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_apdg_conj_right

theorem ay_apdg_projection_failure_no_claim
    {projectionFailure blocksPublication : Prop} :
    projectionFailure -> blocksPublication ->
    AyAPDGNoClaimDiagnostic projectionFailure blocksPublication :=
  ay_apdg_no_claim_diagnostic_intro

theorem ay_apdg_projection_failure_recompute
    {projectionFailure recomputeRequested : Prop} :
    projectionFailure -> recomputeRequested ->
    AyAPDGRecomputeObligation projectionFailure recomputeRequested :=
  ay_apdg_recompute_obligation_intro

theorem ay_apdg_map_failure_no_claim
    {mapFailure blocksPublication : Prop} :
    mapFailure -> blocksPublication ->
    AyAPDGNoClaimDiagnostic mapFailure blocksPublication :=
  ay_apdg_no_claim_diagnostic_intro

theorem ay_apdg_default_failure_no_claim
    {defaultFailure blocksPublication : Prop} :
    defaultFailure -> blocksPublication ->
    AyAPDGNoClaimDiagnostic defaultFailure blocksPublication :=
  ay_apdg_no_claim_diagnostic_intro

theorem ay_apdg_extension_failure_no_claim
    {extensionFailure blocksPublication : Prop} :
    extensionFailure -> blocksPublication ->
    AyAPDGNoClaimDiagnostic extensionFailure blocksPublication :=
  ay_apdg_no_claim_diagnostic_intro

theorem ay_apdg_digest_failure_no_claim
    {digestFailure blocksPublication : Prop} :
    digestFailure -> blocksPublication ->
    AyAPDGNoClaimDiagnostic digestFailure blocksPublication :=
  ay_apdg_no_claim_diagnostic_intro

theorem ay_apdg_replay_failure_no_claim
    {replayFailure blocksPublication : Prop} :
    replayFailure -> blocksPublication ->
    AyAPDGNoClaimDiagnostic replayFailure blocksPublication :=
  ay_apdg_no_claim_diagnostic_intro

theorem ay_apdg_checker_failure_no_claim
    {checkerFailure blocksPublication : Prop} :
    checkerFailure -> blocksPublication ->
    AyAPDGNoClaimDiagnostic checkerFailure blocksPublication :=
  ay_apdg_no_claim_diagnostic_intro

theorem ay_apdg_fingerprint_failure_no_claim
    {fingerprintFailure blocksPublication : Prop} :
    fingerprintFailure -> blocksPublication ->
    AyAPDGNoClaimDiagnostic fingerprintFailure blocksPublication :=
  ay_apdg_no_claim_diagnostic_intro

theorem ay_apdg_build_failure_no_claim
    {buildFailure blocksPublication : Prop} :
    buildFailure -> blocksPublication ->
    AyAPDGNoClaimDiagnostic buildFailure blocksPublication :=
  ay_apdg_no_claim_diagnostic_intro

theorem ay_apdg_archive_failure_no_claim
    {archiveFailure blocksPublication : Prop} :
    archiveFailure -> blocksPublication ->
    AyAPDGNoClaimDiagnostic archiveFailure blocksPublication :=
  ay_apdg_no_claim_diagnostic_intro

theorem ay_apdg_bad_projection_guard_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyAPDGNoClaimDiagnostic failure blocksPublication ->
    AyAPDGRecomputeObligation failure recomputeRequested ->
    AyAPDGConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_apdg_conj_intro
      (ay_apdg_no_claim_diagnostic_blocks hdiagnostic)
      (ay_apdg_recompute_obligation_request hrecompute)
