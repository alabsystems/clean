/- SAT-COMP/ay partial-assignment completion manifest contract.

This file is self-contained and propositional.  It models when a partial SAT
assignment may be completed and published as an original-formula SAT witness.
-/

def AyPACMConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyPACMDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyPACMEquisat (source target : Prop) : Prop :=
  AyPACMConj (source -> target) (target -> source)

def AyPACMCompletionManifest
    (partialAssignment completedAssignment completionAgreement : Prop) : Prop :=
  AyPACMConj partialAssignment
    (AyPACMConj completedAssignment completionAgreement)

def AyPACMDefaultLiteralPolicy
    (defaultPolicy defaultLiterals defaultAgreement : Prop) : Prop :=
  AyPACMConj defaultPolicy (AyPACMConj defaultLiterals defaultAgreement)

def AyPACMDimacsMap
    (internalToDimacs dimacsToInternal mapAgreement : Prop) : Prop :=
  AyPACMConj internalToDimacs (AyPACMConj dimacsToInternal mapAgreement)

def AyPACMExtensionWitnessLedger
    (extensionWitness extensionLedger extensionAgreement : Prop) : Prop :=
  AyPACMConj extensionWitness
    (AyPACMConj extensionLedger extensionAgreement)

def AyPACMAssignmentDigest
    (partialDigest completedDigest digestAgreement : Prop) : Prop :=
  AyPACMConj partialDigest (AyPACMConj completedDigest digestAgreement)

def AyPACMClauseReplay
    (clauseReplay completedEvaluation replayAgreement : Prop) : Prop :=
  AyPACMConj clauseReplay (AyPACMConj completedEvaluation replayAgreement)

def AyPACMCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AyPACMConj checkerAccepted (AyPACMConj transcript transcriptAgreement)

def AyPACMFormulaFingerprint
    (originalFingerprint completionFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyPACMConj originalFingerprint
    (AyPACMConj completionFingerprint fingerprintAgreement)

def AyPACMBuildEvidence
    (solverBuild completionBuild buildAgreement : Prop) : Prop :=
  AyPACMConj solverBuild (AyPACMConj completionBuild buildAgreement)

def AyPACMArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AyPACMConj archiveEntry (AyPACMConj archiveDigest archiveAgreement)

def AyPACMAcceptedCompletion
    (completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AyPACMConj completionOk
    (AyPACMConj defaultOk
      (AyPACMConj mapOk
        (AyPACMConj extensionOk
          (AyPACMConj digestOk
            (AyPACMConj replayOk
              (AyPACMConj checkerOk
                (AyPACMConj fingerprintOk
                  (AyPACMConj buildOk archiveOk))))))))

def AyPACMPublicSatWitness
    (acceptedCompletion completedWitness publicSatClaim : Prop) : Prop :=
  AyPACMConj acceptedCompletion (AyPACMConj completedWitness publicSatClaim)

def AyPACMNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AyPACMConj reason blocksPublication

def AyPACMRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AyPACMConj reason recomputeRequested

theorem ay_pacm_conj_intro {left right : Prop} :
    left -> right -> AyPACMConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_pacm_conj_left {left right : Prop} :
    AyPACMConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_pacm_conj_right {left right : Prop} :
    AyPACMConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_pacm_disj_left {left right : Prop} :
    left -> AyPACMDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_pacm_disj_right {left right : Prop} :
    right -> AyPACMDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_pacm_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AyPACMEquisat source target :=
  fun forward backward => ay_pacm_conj_intro forward backward

theorem ay_pacm_equisat_forward {source target : Prop} :
    AyPACMEquisat source target -> source -> target :=
  fun h => ay_pacm_conj_left h

theorem ay_pacm_equisat_backward {source target : Prop} :
    AyPACMEquisat source target -> target -> source :=
  fun h => ay_pacm_conj_right h

theorem ay_pacm_completion_manifest_intro
    {partialAssignment completedAssignment completionAgreement : Prop} :
    partialAssignment -> completedAssignment -> completionAgreement ->
    AyPACMCompletionManifest
      partialAssignment completedAssignment completionAgreement :=
  fun hpartial hcompleted hagree =>
    ay_pacm_conj_intro hpartial (ay_pacm_conj_intro hcompleted hagree)

theorem ay_pacm_completion_manifest_partial
    {partialAssignment completedAssignment completionAgreement : Prop} :
    AyPACMCompletionManifest
      partialAssignment completedAssignment completionAgreement ->
    partialAssignment :=
  fun h => ay_pacm_conj_left h

theorem ay_pacm_completion_manifest_completed
    {partialAssignment completedAssignment completionAgreement : Prop} :
    AyPACMCompletionManifest
      partialAssignment completedAssignment completionAgreement ->
    completedAssignment :=
  fun h => ay_pacm_conj_left (ay_pacm_conj_right h)

theorem ay_pacm_completion_manifest_agreement
    {partialAssignment completedAssignment completionAgreement : Prop} :
    AyPACMCompletionManifest
      partialAssignment completedAssignment completionAgreement ->
    completionAgreement :=
  fun h => ay_pacm_conj_right (ay_pacm_conj_right h)

theorem ay_pacm_default_literal_policy_intro
    {defaultPolicy defaultLiterals defaultAgreement : Prop} :
    defaultPolicy -> defaultLiterals -> defaultAgreement ->
    AyPACMDefaultLiteralPolicy defaultPolicy defaultLiterals defaultAgreement :=
  fun hpolicy hliterals hagree =>
    ay_pacm_conj_intro hpolicy (ay_pacm_conj_intro hliterals hagree)

theorem ay_pacm_dimacs_map_intro
    {internalToDimacs dimacsToInternal mapAgreement : Prop} :
    internalToDimacs -> dimacsToInternal -> mapAgreement ->
    AyPACMDimacsMap internalToDimacs dimacsToInternal mapAgreement :=
  fun hforward hbackward hagree =>
    ay_pacm_conj_intro hforward (ay_pacm_conj_intro hbackward hagree)

theorem ay_pacm_extension_witness_ledger_intro
    {extensionWitness extensionLedger extensionAgreement : Prop} :
    extensionWitness -> extensionLedger -> extensionAgreement ->
    AyPACMExtensionWitnessLedger
      extensionWitness extensionLedger extensionAgreement :=
  fun hwitness hledger hagree =>
    ay_pacm_conj_intro hwitness (ay_pacm_conj_intro hledger hagree)

theorem ay_pacm_assignment_digest_intro
    {partialDigest completedDigest digestAgreement : Prop} :
    partialDigest -> completedDigest -> digestAgreement ->
    AyPACMAssignmentDigest partialDigest completedDigest digestAgreement :=
  fun hpartial hcompleted hagree =>
    ay_pacm_conj_intro hpartial (ay_pacm_conj_intro hcompleted hagree)

theorem ay_pacm_clause_replay_intro
    {clauseReplay completedEvaluation replayAgreement : Prop} :
    clauseReplay -> completedEvaluation -> replayAgreement ->
    AyPACMClauseReplay clauseReplay completedEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_pacm_conj_intro hreplay (ay_pacm_conj_intro heval hagree)

theorem ay_pacm_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AyPACMCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_pacm_conj_intro haccepted (ay_pacm_conj_intro htranscript hagree)

theorem ay_pacm_formula_fingerprint_intro
    {originalFingerprint completionFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> completionFingerprint -> fingerprintAgreement ->
    AyPACMFormulaFingerprint
      originalFingerprint completionFingerprint fingerprintAgreement :=
  fun horiginal hcompletion hagree =>
    ay_pacm_conj_intro horiginal (ay_pacm_conj_intro hcompletion hagree)

theorem ay_pacm_build_evidence_intro
    {solverBuild completionBuild buildAgreement : Prop} :
    solverBuild -> completionBuild -> buildAgreement ->
    AyPACMBuildEvidence solverBuild completionBuild buildAgreement :=
  fun hsolver hcompletion hagree =>
    ay_pacm_conj_intro hsolver (ay_pacm_conj_intro hcompletion hagree)

theorem ay_pacm_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AyPACMArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_pacm_conj_intro hentry (ay_pacm_conj_intro hdigest hagree)

theorem ay_pacm_accepted_completion_intro
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    completionOk -> defaultOk -> mapOk -> extensionOk -> digestOk ->
    replayOk -> checkerOk -> fingerprintOk -> buildOk -> archiveOk ->
    AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk :=
  fun hcompletion hdefault hmap hextension hdigest hreplay hchecker
      hfingerprint hbuild harchive =>
    ay_pacm_conj_intro hcompletion
      (ay_pacm_conj_intro hdefault
        (ay_pacm_conj_intro hmap
          (ay_pacm_conj_intro hextension
            (ay_pacm_conj_intro hdigest
              (ay_pacm_conj_intro hreplay
                (ay_pacm_conj_intro hchecker
                  (ay_pacm_conj_intro hfingerprint
                    (ay_pacm_conj_intro hbuild harchive))))))))

theorem ay_pacm_accepted_completion_completion
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    completionOk :=
  fun h => ay_pacm_conj_left h

theorem ay_pacm_accepted_completion_default
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    defaultOk :=
  fun h => ay_pacm_conj_left (ay_pacm_conj_right h)

theorem ay_pacm_accepted_completion_map
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    mapOk :=
  fun h => ay_pacm_conj_left (ay_pacm_conj_right (ay_pacm_conj_right h))

theorem ay_pacm_accepted_completion_extension
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    extensionOk :=
  fun h =>
    ay_pacm_conj_left
      (ay_pacm_conj_right (ay_pacm_conj_right (ay_pacm_conj_right h)))

theorem ay_pacm_accepted_completion_digest
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    digestOk :=
  fun h =>
    ay_pacm_conj_left
      (ay_pacm_conj_right
        (ay_pacm_conj_right (ay_pacm_conj_right (ay_pacm_conj_right h))))

theorem ay_pacm_accepted_completion_replay
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    replayOk :=
  fun h =>
    ay_pacm_conj_left
      (ay_pacm_conj_right
        (ay_pacm_conj_right
          (ay_pacm_conj_right (ay_pacm_conj_right
            (ay_pacm_conj_right h)))))

theorem ay_pacm_accepted_completion_checker
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_pacm_conj_left
      (ay_pacm_conj_right
        (ay_pacm_conj_right
          (ay_pacm_conj_right
            (ay_pacm_conj_right (ay_pacm_conj_right
              (ay_pacm_conj_right h))))))

theorem ay_pacm_accepted_completion_fingerprint
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_pacm_conj_left
      (ay_pacm_conj_right
        (ay_pacm_conj_right
          (ay_pacm_conj_right
            (ay_pacm_conj_right
              (ay_pacm_conj_right (ay_pacm_conj_right
                (ay_pacm_conj_right h)))))))

theorem ay_pacm_accepted_completion_build
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_pacm_conj_left
      (ay_pacm_conj_right
        (ay_pacm_conj_right
          (ay_pacm_conj_right
            (ay_pacm_conj_right
              (ay_pacm_conj_right
                (ay_pacm_conj_right (ay_pacm_conj_right
                  (ay_pacm_conj_right h))))))))

theorem ay_pacm_accepted_completion_archive
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_pacm_conj_right
      (ay_pacm_conj_right
        (ay_pacm_conj_right
          (ay_pacm_conj_right
            (ay_pacm_conj_right
              (ay_pacm_conj_right
                (ay_pacm_conj_right (ay_pacm_conj_right
                  (ay_pacm_conj_right h))))))))

theorem ay_pacm_public_sat_witness_intro
    {acceptedCompletion completedWitness publicSatClaim : Prop} :
    acceptedCompletion -> completedWitness -> publicSatClaim ->
    AyPACMPublicSatWitness acceptedCompletion completedWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_pacm_conj_intro hevidence (ay_pacm_conj_intro hwitness hclaim)

theorem ay_pacm_public_sat_witness_evidence
    {acceptedCompletion completedWitness publicSatClaim : Prop} :
    AyPACMPublicSatWitness acceptedCompletion completedWitness publicSatClaim ->
    acceptedCompletion :=
  fun h => ay_pacm_conj_left h

theorem ay_pacm_public_sat_witness_claim
    {acceptedCompletion completedWitness publicSatClaim : Prop} :
    AyPACMPublicSatWitness acceptedCompletion completedWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_pacm_conj_right (ay_pacm_conj_right h)

theorem ay_pacm_accepted_completion_publishes_sound_sat
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk completedWitness publicSatClaim : Prop} :
    AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    completedWitness -> publicSatClaim ->
    AyPACMPublicSatWitness
      (AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      completedWitness publicSatClaim :=
  ay_pacm_public_sat_witness_intro

theorem ay_pacm_completion_preserves_original_truth
    {partialTruth originalTruth : Prop} :
    AyPACMEquisat partialTruth originalTruth -> partialTruth -> originalTruth :=
  ay_pacm_equisat_forward

theorem ay_pacm_public_sat_requires_accepted_completion
    {acceptedCompletion completedWitness publicSatClaim : Prop} :
    AyPACMPublicSatWitness acceptedCompletion completedWitness publicSatClaim ->
    acceptedCompletion :=
  ay_pacm_public_sat_witness_evidence

theorem ay_pacm_publication_requires_completion
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk completedWitness publicSatClaim : Prop} :
    AyPACMPublicSatWitness
      (AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      completedWitness publicSatClaim ->
    completionOk :=
  fun h => ay_pacm_accepted_completion_completion
    (ay_pacm_public_sat_witness_evidence h)

theorem ay_pacm_publication_requires_default
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk completedWitness publicSatClaim : Prop} :
    AyPACMPublicSatWitness
      (AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      completedWitness publicSatClaim ->
    defaultOk :=
  fun h => ay_pacm_accepted_completion_default
    (ay_pacm_public_sat_witness_evidence h)

theorem ay_pacm_publication_requires_map
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk completedWitness publicSatClaim : Prop} :
    AyPACMPublicSatWitness
      (AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      completedWitness publicSatClaim ->
    mapOk :=
  fun h => ay_pacm_accepted_completion_map
    (ay_pacm_public_sat_witness_evidence h)

theorem ay_pacm_publication_requires_extension
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk completedWitness publicSatClaim : Prop} :
    AyPACMPublicSatWitness
      (AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      completedWitness publicSatClaim ->
    extensionOk :=
  fun h => ay_pacm_accepted_completion_extension
    (ay_pacm_public_sat_witness_evidence h)

theorem ay_pacm_publication_requires_digest
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk completedWitness publicSatClaim : Prop} :
    AyPACMPublicSatWitness
      (AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      completedWitness publicSatClaim ->
    digestOk :=
  fun h => ay_pacm_accepted_completion_digest
    (ay_pacm_public_sat_witness_evidence h)

theorem ay_pacm_publication_requires_replay
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk completedWitness publicSatClaim : Prop} :
    AyPACMPublicSatWitness
      (AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      completedWitness publicSatClaim ->
    replayOk :=
  fun h => ay_pacm_accepted_completion_replay
    (ay_pacm_public_sat_witness_evidence h)

theorem ay_pacm_publication_requires_checker
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk completedWitness publicSatClaim : Prop} :
    AyPACMPublicSatWitness
      (AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      completedWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_pacm_accepted_completion_checker
    (ay_pacm_public_sat_witness_evidence h)

theorem ay_pacm_publication_requires_fingerprint
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk completedWitness publicSatClaim : Prop} :
    AyPACMPublicSatWitness
      (AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      completedWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_pacm_accepted_completion_fingerprint
    (ay_pacm_public_sat_witness_evidence h)

theorem ay_pacm_publication_requires_build
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk completedWitness publicSatClaim : Prop} :
    AyPACMPublicSatWitness
      (AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      completedWitness publicSatClaim ->
    buildOk :=
  fun h => ay_pacm_accepted_completion_build
    (ay_pacm_public_sat_witness_evidence h)

theorem ay_pacm_publication_requires_archive
    {completionOk defaultOk mapOk extensionOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk completedWitness publicSatClaim : Prop} :
    AyPACMPublicSatWitness
      (AyPACMAcceptedCompletion completionOk defaultOk mapOk extensionOk
        digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      completedWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_pacm_accepted_completion_archive
    (ay_pacm_public_sat_witness_evidence h)

theorem ay_pacm_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AyPACMNoClaimDiagnostic reason blocksPublication :=
  ay_pacm_conj_intro

theorem ay_pacm_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AyPACMNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_pacm_conj_right

theorem ay_pacm_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AyPACMRecomputeObligation reason recomputeRequested :=
  ay_pacm_conj_intro

theorem ay_pacm_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AyPACMRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_pacm_conj_right

theorem ay_pacm_completion_failure_no_claim
    {completionFailure blocksPublication : Prop} :
    completionFailure -> blocksPublication ->
    AyPACMNoClaimDiagnostic completionFailure blocksPublication :=
  ay_pacm_no_claim_diagnostic_intro

theorem ay_pacm_completion_failure_recompute
    {completionFailure recomputeRequested : Prop} :
    completionFailure -> recomputeRequested ->
    AyPACMRecomputeObligation completionFailure recomputeRequested :=
  ay_pacm_recompute_obligation_intro

theorem ay_pacm_default_failure_no_claim
    {defaultFailure blocksPublication : Prop} :
    defaultFailure -> blocksPublication ->
    AyPACMNoClaimDiagnostic defaultFailure blocksPublication :=
  ay_pacm_no_claim_diagnostic_intro

theorem ay_pacm_map_failure_no_claim
    {mapFailure blocksPublication : Prop} :
    mapFailure -> blocksPublication ->
    AyPACMNoClaimDiagnostic mapFailure blocksPublication :=
  ay_pacm_no_claim_diagnostic_intro

theorem ay_pacm_extension_failure_no_claim
    {extensionFailure blocksPublication : Prop} :
    extensionFailure -> blocksPublication ->
    AyPACMNoClaimDiagnostic extensionFailure blocksPublication :=
  ay_pacm_no_claim_diagnostic_intro

theorem ay_pacm_digest_failure_no_claim
    {digestFailure blocksPublication : Prop} :
    digestFailure -> blocksPublication ->
    AyPACMNoClaimDiagnostic digestFailure blocksPublication :=
  ay_pacm_no_claim_diagnostic_intro

theorem ay_pacm_replay_failure_no_claim
    {replayFailure blocksPublication : Prop} :
    replayFailure -> blocksPublication ->
    AyPACMNoClaimDiagnostic replayFailure blocksPublication :=
  ay_pacm_no_claim_diagnostic_intro

theorem ay_pacm_checker_failure_no_claim
    {checkerFailure blocksPublication : Prop} :
    checkerFailure -> blocksPublication ->
    AyPACMNoClaimDiagnostic checkerFailure blocksPublication :=
  ay_pacm_no_claim_diagnostic_intro

theorem ay_pacm_fingerprint_failure_no_claim
    {fingerprintFailure blocksPublication : Prop} :
    fingerprintFailure -> blocksPublication ->
    AyPACMNoClaimDiagnostic fingerprintFailure blocksPublication :=
  ay_pacm_no_claim_diagnostic_intro

theorem ay_pacm_build_failure_no_claim
    {buildFailure blocksPublication : Prop} :
    buildFailure -> blocksPublication ->
    AyPACMNoClaimDiagnostic buildFailure blocksPublication :=
  ay_pacm_no_claim_diagnostic_intro

theorem ay_pacm_archive_failure_no_claim
    {archiveFailure blocksPublication : Prop} :
    archiveFailure -> blocksPublication ->
    AyPACMNoClaimDiagnostic archiveFailure blocksPublication :=
  ay_pacm_no_claim_diagnostic_intro

theorem ay_pacm_bad_completion_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AyPACMNoClaimDiagnostic failure blocksPublication ->
    AyPACMRecomputeObligation failure recomputeRequested ->
    AyPACMConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_pacm_conj_intro
      (ay_pacm_no_claim_diagnostic_blocks hdiagnostic)
      (ay_pacm_recompute_obligation_request hrecompute)
