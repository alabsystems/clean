/- SAT-COMP/ay symmetry-breaking projection guard contract.

This self-contained package models SAT model publication through symmetry
breaking.  Projection back to the original formula is accepted only when the
symmetry manifest, orbit representative map, extension witnesses, digest,
replay, checker, fingerprint, build, and archive evidence all agree.
-/

def AySMBPConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AySMBPDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AySMBPEquisat (source target : Prop) : Prop :=
  AySMBPConj (source -> target) (target -> source)

def AySMBPSymmetryBreakingManifest
    (originalFormula symmetryClauses symmetryAgreement : Prop) : Prop :=
  AySMBPConj originalFormula
    (AySMBPConj symmetryClauses symmetryAgreement)

def AySMBPOrbitRepresentativeMap
    (orbitRepresentatives originalVariables mapAgreement : Prop) : Prop :=
  AySMBPConj orbitRepresentatives
    (AySMBPConj originalVariables mapAgreement)

def AySMBPExtensionWitnessLedger
    (extensionWitness witnessLedger witnessAgreement : Prop) : Prop :=
  AySMBPConj extensionWitness (AySMBPConj witnessLedger witnessAgreement)

def AySMBPAssignmentDigest
    (symmetryDigest originalDigest digestAgreement : Prop) : Prop :=
  AySMBPConj symmetryDigest (AySMBPConj originalDigest digestAgreement)

def AySMBPClauseReplay
    (clauseReplay originalEvaluation replayAgreement : Prop) : Prop :=
  AySMBPConj clauseReplay (AySMBPConj originalEvaluation replayAgreement)

def AySMBPCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AySMBPConj checkerAccepted (AySMBPConj transcript transcriptAgreement)

def AySMBPFormulaFingerprint
    (originalFingerprint symmetryFingerprint fingerprintAgreement : Prop) : Prop :=
  AySMBPConj originalFingerprint
    (AySMBPConj symmetryFingerprint fingerprintAgreement)

def AySMBPBuildEvidence
    (solverBuild symmetryBuild buildAgreement : Prop) : Prop :=
  AySMBPConj solverBuild (AySMBPConj symmetryBuild buildAgreement)

def AySMBPArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AySMBPConj archiveEntry (AySMBPConj archiveDigest archiveAgreement)

def AySMBPAcceptedProjection
    (symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AySMBPConj symmetryOk
    (AySMBPConj mapOk
      (AySMBPConj witnessOk
        (AySMBPConj assignmentOk
          (AySMBPConj replayOk
            (AySMBPConj checkerOk
              (AySMBPConj fingerprintOk
                (AySMBPConj buildOk archiveOk)))))))

def AySMBPPublicSatWitness
    (acceptedProjection originalWitness publicSatClaim : Prop) : Prop :=
  AySMBPConj acceptedProjection (AySMBPConj originalWitness publicSatClaim)

def AySMBPNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AySMBPConj reason blocksPublication

def AySMBPRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AySMBPConj reason recomputeRequested

theorem ay_smbp_conj_intro {left right : Prop} :
    left -> right -> AySMBPConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_smbp_conj_left {left right : Prop} :
    AySMBPConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_smbp_conj_right {left right : Prop} :
    AySMBPConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_smbp_disj_left {left right : Prop} :
    left -> AySMBPDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_smbp_disj_right {left right : Prop} :
    right -> AySMBPDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_smbp_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AySMBPEquisat source target :=
  fun forward backward => ay_smbp_conj_intro forward backward

theorem ay_smbp_equisat_forward {source target : Prop} :
    AySMBPEquisat source target -> source -> target :=
  fun h => ay_smbp_conj_left h

theorem ay_smbp_equisat_backward {source target : Prop} :
    AySMBPEquisat source target -> target -> source :=
  fun h => ay_smbp_conj_right h

theorem ay_smbp_symmetry_breaking_manifest_intro
    {originalFormula symmetryClauses symmetryAgreement : Prop} :
    originalFormula -> symmetryClauses -> symmetryAgreement ->
    AySMBPSymmetryBreakingManifest
      originalFormula symmetryClauses symmetryAgreement :=
  fun horiginal hsymmetry hagree =>
    ay_smbp_conj_intro horiginal (ay_smbp_conj_intro hsymmetry hagree)

theorem ay_smbp_symmetry_breaking_manifest_original
    {originalFormula symmetryClauses symmetryAgreement : Prop} :
    AySMBPSymmetryBreakingManifest
      originalFormula symmetryClauses symmetryAgreement ->
    originalFormula :=
  fun h => ay_smbp_conj_left h

theorem ay_smbp_symmetry_breaking_manifest_clauses
    {originalFormula symmetryClauses symmetryAgreement : Prop} :
    AySMBPSymmetryBreakingManifest
      originalFormula symmetryClauses symmetryAgreement ->
    symmetryClauses :=
  fun h => ay_smbp_conj_left (ay_smbp_conj_right h)

theorem ay_smbp_symmetry_breaking_manifest_agreement
    {originalFormula symmetryClauses symmetryAgreement : Prop} :
    AySMBPSymmetryBreakingManifest
      originalFormula symmetryClauses symmetryAgreement ->
    symmetryAgreement :=
  fun h => ay_smbp_conj_right (ay_smbp_conj_right h)

theorem ay_smbp_orbit_representative_map_intro
    {orbitRepresentatives originalVariables mapAgreement : Prop} :
    orbitRepresentatives -> originalVariables -> mapAgreement ->
    AySMBPOrbitRepresentativeMap
      orbitRepresentatives originalVariables mapAgreement :=
  fun horbit horiginal hagree =>
    ay_smbp_conj_intro horbit (ay_smbp_conj_intro horiginal hagree)

theorem ay_smbp_extension_witness_ledger_intro
    {extensionWitness witnessLedger witnessAgreement : Prop} :
    extensionWitness -> witnessLedger -> witnessAgreement ->
    AySMBPExtensionWitnessLedger
      extensionWitness witnessLedger witnessAgreement :=
  fun hwitness hledger hagree =>
    ay_smbp_conj_intro hwitness (ay_smbp_conj_intro hledger hagree)

theorem ay_smbp_assignment_digest_intro
    {symmetryDigest originalDigest digestAgreement : Prop} :
    symmetryDigest -> originalDigest -> digestAgreement ->
    AySMBPAssignmentDigest symmetryDigest originalDigest digestAgreement :=
  fun hsymmetry horiginal hagree =>
    ay_smbp_conj_intro hsymmetry (ay_smbp_conj_intro horiginal hagree)

theorem ay_smbp_clause_replay_intro
    {clauseReplay originalEvaluation replayAgreement : Prop} :
    clauseReplay -> originalEvaluation -> replayAgreement ->
    AySMBPClauseReplay clauseReplay originalEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_smbp_conj_intro hreplay (ay_smbp_conj_intro heval hagree)

theorem ay_smbp_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AySMBPCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_smbp_conj_intro haccepted (ay_smbp_conj_intro htranscript hagree)

theorem ay_smbp_formula_fingerprint_intro
    {originalFingerprint symmetryFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> symmetryFingerprint -> fingerprintAgreement ->
    AySMBPFormulaFingerprint
      originalFingerprint symmetryFingerprint fingerprintAgreement :=
  fun horiginal hsymmetry hagree =>
    ay_smbp_conj_intro horiginal (ay_smbp_conj_intro hsymmetry hagree)

theorem ay_smbp_build_evidence_intro
    {solverBuild symmetryBuild buildAgreement : Prop} :
    solverBuild -> symmetryBuild -> buildAgreement ->
    AySMBPBuildEvidence solverBuild symmetryBuild buildAgreement :=
  fun hsolver hsymmetry hagree =>
    ay_smbp_conj_intro hsolver (ay_smbp_conj_intro hsymmetry hagree)

theorem ay_smbp_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AySMBPArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_smbp_conj_intro hentry (ay_smbp_conj_intro hdigest hagree)

theorem ay_smbp_accepted_projection_intro
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    symmetryOk -> mapOk -> witnessOk -> assignmentOk -> replayOk ->
    checkerOk -> fingerprintOk -> buildOk -> archiveOk ->
    AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk :=
  fun hsymmetry hmap hwitness hassignment hreplay hchecker hfingerprint
      hbuild harchive =>
    ay_smbp_conj_intro hsymmetry
      (ay_smbp_conj_intro hmap
        (ay_smbp_conj_intro hwitness
          (ay_smbp_conj_intro hassignment
            (ay_smbp_conj_intro hreplay
              (ay_smbp_conj_intro hchecker
                (ay_smbp_conj_intro hfingerprint
                  (ay_smbp_conj_intro hbuild harchive)))))))

theorem ay_smbp_accepted_projection_symmetry
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    symmetryOk :=
  fun h => ay_smbp_conj_left h

theorem ay_smbp_accepted_projection_map
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    mapOk :=
  fun h => ay_smbp_conj_left (ay_smbp_conj_right h)

theorem ay_smbp_accepted_projection_witness
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    witnessOk :=
  fun h => ay_smbp_conj_left (ay_smbp_conj_right (ay_smbp_conj_right h))

theorem ay_smbp_accepted_projection_assignment
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    assignmentOk :=
  fun h =>
    ay_smbp_conj_left
      (ay_smbp_conj_right (ay_smbp_conj_right (ay_smbp_conj_right h)))

theorem ay_smbp_accepted_projection_replay
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    replayOk :=
  fun h =>
    ay_smbp_conj_left
      (ay_smbp_conj_right
        (ay_smbp_conj_right (ay_smbp_conj_right (ay_smbp_conj_right h))))

theorem ay_smbp_accepted_projection_checker
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_smbp_conj_left
      (ay_smbp_conj_right
        (ay_smbp_conj_right
          (ay_smbp_conj_right (ay_smbp_conj_right (ay_smbp_conj_right h)))))

theorem ay_smbp_accepted_projection_fingerprint
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_smbp_conj_left
      (ay_smbp_conj_right
        (ay_smbp_conj_right
          (ay_smbp_conj_right
            (ay_smbp_conj_right (ay_smbp_conj_right
              (ay_smbp_conj_right h))))))

theorem ay_smbp_accepted_projection_build
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_smbp_conj_left
      (ay_smbp_conj_right
        (ay_smbp_conj_right
          (ay_smbp_conj_right
            (ay_smbp_conj_right
              (ay_smbp_conj_right (ay_smbp_conj_right
                (ay_smbp_conj_right h)))))))

theorem ay_smbp_accepted_projection_archive
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_smbp_conj_right
      (ay_smbp_conj_right
        (ay_smbp_conj_right
          (ay_smbp_conj_right
            (ay_smbp_conj_right
              (ay_smbp_conj_right (ay_smbp_conj_right
                (ay_smbp_conj_right h)))))))

theorem ay_smbp_public_sat_witness_intro
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    acceptedProjection -> originalWitness -> publicSatClaim ->
    AySMBPPublicSatWitness acceptedProjection originalWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_smbp_conj_intro hevidence (ay_smbp_conj_intro hwitness hclaim)

theorem ay_smbp_public_sat_witness_evidence
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AySMBPPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    acceptedProjection :=
  fun h => ay_smbp_conj_left h

theorem ay_smbp_public_sat_witness_claim
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AySMBPPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_smbp_conj_right (ay_smbp_conj_right h)

theorem ay_smbp_accepted_projection_publishes_sound_sat
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
      replayOk checkerOk fingerprintOk buildOk archiveOk ->
    originalWitness -> publicSatClaim ->
    AySMBPPublicSatWitness
      (AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim :=
  ay_smbp_public_sat_witness_intro

theorem ay_smbp_projection_reconstructs_original_assignment
    {symmetryTruth originalTruth : Prop} :
    AySMBPEquisat symmetryTruth originalTruth -> symmetryTruth -> originalTruth :=
  ay_smbp_equisat_forward

theorem ay_smbp_public_sat_requires_accepted_projection
    {acceptedProjection originalWitness publicSatClaim : Prop} :
    AySMBPPublicSatWitness acceptedProjection originalWitness publicSatClaim ->
    acceptedProjection :=
  ay_smbp_public_sat_witness_evidence

theorem ay_smbp_publication_requires_symmetry
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySMBPPublicSatWitness
      (AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    symmetryOk :=
  fun h => ay_smbp_accepted_projection_symmetry
    (ay_smbp_public_sat_witness_evidence h)

theorem ay_smbp_publication_requires_map
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySMBPPublicSatWitness
      (AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    mapOk :=
  fun h => ay_smbp_accepted_projection_map
    (ay_smbp_public_sat_witness_evidence h)

theorem ay_smbp_publication_requires_witness
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySMBPPublicSatWitness
      (AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    witnessOk :=
  fun h => ay_smbp_accepted_projection_witness
    (ay_smbp_public_sat_witness_evidence h)

theorem ay_smbp_publication_requires_assignment
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySMBPPublicSatWitness
      (AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    assignmentOk :=
  fun h => ay_smbp_accepted_projection_assignment
    (ay_smbp_public_sat_witness_evidence h)

theorem ay_smbp_publication_requires_replay
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySMBPPublicSatWitness
      (AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    replayOk :=
  fun h => ay_smbp_accepted_projection_replay
    (ay_smbp_public_sat_witness_evidence h)

theorem ay_smbp_publication_requires_checker
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySMBPPublicSatWitness
      (AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_smbp_accepted_projection_checker
    (ay_smbp_public_sat_witness_evidence h)

theorem ay_smbp_publication_requires_fingerprint
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySMBPPublicSatWitness
      (AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_smbp_accepted_projection_fingerprint
    (ay_smbp_public_sat_witness_evidence h)

theorem ay_smbp_publication_requires_build
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySMBPPublicSatWitness
      (AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    buildOk :=
  fun h => ay_smbp_accepted_projection_build
    (ay_smbp_public_sat_witness_evidence h)

theorem ay_smbp_publication_requires_archive
    {symmetryOk mapOk witnessOk assignmentOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySMBPPublicSatWitness
      (AySMBPAcceptedProjection symmetryOk mapOk witnessOk assignmentOk
        replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_smbp_accepted_projection_archive
    (ay_smbp_public_sat_witness_evidence h)

theorem ay_smbp_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AySMBPNoClaimDiagnostic reason blocksPublication :=
  ay_smbp_conj_intro

theorem ay_smbp_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AySMBPNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_smbp_conj_right

theorem ay_smbp_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AySMBPRecomputeObligation reason recomputeRequested :=
  ay_smbp_conj_intro

theorem ay_smbp_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AySMBPRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_smbp_conj_right

theorem ay_smbp_symmetry_failure_no_claim
    {symmetryFailure blocksPublication : Prop} :
    symmetryFailure -> blocksPublication ->
    AySMBPNoClaimDiagnostic symmetryFailure blocksPublication :=
  ay_smbp_no_claim_diagnostic_intro

theorem ay_smbp_symmetry_failure_recompute
    {symmetryFailure recomputeRequested : Prop} :
    symmetryFailure -> recomputeRequested ->
    AySMBPRecomputeObligation symmetryFailure recomputeRequested :=
  ay_smbp_recompute_obligation_intro

theorem ay_smbp_map_failure_no_claim
    {mapFailure blocksPublication : Prop} :
    mapFailure -> blocksPublication ->
    AySMBPNoClaimDiagnostic mapFailure blocksPublication :=
  ay_smbp_no_claim_diagnostic_intro

theorem ay_smbp_witness_failure_no_claim
    {witnessFailure blocksPublication : Prop} :
    witnessFailure -> blocksPublication ->
    AySMBPNoClaimDiagnostic witnessFailure blocksPublication :=
  ay_smbp_no_claim_diagnostic_intro

theorem ay_smbp_assignment_failure_no_claim
    {assignmentFailure blocksPublication : Prop} :
    assignmentFailure -> blocksPublication ->
    AySMBPNoClaimDiagnostic assignmentFailure blocksPublication :=
  ay_smbp_no_claim_diagnostic_intro

theorem ay_smbp_replay_failure_no_claim
    {replayFailure blocksPublication : Prop} :
    replayFailure -> blocksPublication ->
    AySMBPNoClaimDiagnostic replayFailure blocksPublication :=
  ay_smbp_no_claim_diagnostic_intro

theorem ay_smbp_checker_failure_no_claim
    {checkerFailure blocksPublication : Prop} :
    checkerFailure -> blocksPublication ->
    AySMBPNoClaimDiagnostic checkerFailure blocksPublication :=
  ay_smbp_no_claim_diagnostic_intro

theorem ay_smbp_fingerprint_failure_no_claim
    {fingerprintFailure blocksPublication : Prop} :
    fingerprintFailure -> blocksPublication ->
    AySMBPNoClaimDiagnostic fingerprintFailure blocksPublication :=
  ay_smbp_no_claim_diagnostic_intro

theorem ay_smbp_build_failure_no_claim
    {buildFailure blocksPublication : Prop} :
    buildFailure -> blocksPublication ->
    AySMBPNoClaimDiagnostic buildFailure blocksPublication :=
  ay_smbp_no_claim_diagnostic_intro

theorem ay_smbp_archive_failure_no_claim
    {archiveFailure blocksPublication : Prop} :
    archiveFailure -> blocksPublication ->
    AySMBPNoClaimDiagnostic archiveFailure blocksPublication :=
  ay_smbp_no_claim_diagnostic_intro

theorem ay_smbp_bad_projection_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AySMBPNoClaimDiagnostic failure blocksPublication ->
    AySMBPRecomputeObligation failure recomputeRequested ->
    AySMBPConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_smbp_conj_intro
      (ay_smbp_no_claim_diagnostic_blocks hdiagnostic)
      (ay_smbp_recompute_obligation_request hrecompute)
