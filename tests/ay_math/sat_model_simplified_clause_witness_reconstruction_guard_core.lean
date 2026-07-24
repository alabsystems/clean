/- SAT-COMP/ay simplified-clause witness reconstruction guard contract.

This self-contained package models SAT model publication after clause
simplification.  A reconstructed witness may be published only when the
simplification manifest, removed-clause witness ledger, projection evidence,
DIMACS map, digest, replay, checker, fingerprint, build, and archive evidence
all agree.
-/

def AySCWRConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AySCWRDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AySCWREquisat (source target : Prop) : Prop :=
  AySCWRConj (source -> target) (target -> source)

def AySCWRSimplificationManifest
    (originalClauses simplifiedClauses simplificationAgreement : Prop) : Prop :=
  AySCWRConj originalClauses
    (AySCWRConj simplifiedClauses simplificationAgreement)

def AySCWRRemovedClauseWitnessLedger
    (removedClauses witnessLedger witnessAgreement : Prop) : Prop :=
  AySCWRConj removedClauses (AySCWRConj witnessLedger witnessAgreement)

def AySCWRProjectionManifest
    (simplifiedWitness originalWitness projectionAgreement : Prop) : Prop :=
  AySCWRConj simplifiedWitness
    (AySCWRConj originalWitness projectionAgreement)

def AySCWRDimacsMap
    (internalToDimacs dimacsToInternal mapAgreement : Prop) : Prop :=
  AySCWRConj internalToDimacs (AySCWRConj dimacsToInternal mapAgreement)

def AySCWRAssignmentDigest
    (simplifiedDigest originalDigest digestAgreement : Prop) : Prop :=
  AySCWRConj simplifiedDigest (AySCWRConj originalDigest digestAgreement)

def AySCWRClauseReplay
    (clauseReplay originalEvaluation replayAgreement : Prop) : Prop :=
  AySCWRConj clauseReplay (AySCWRConj originalEvaluation replayAgreement)

def AySCWRCheckerTranscript
    (checkerAccepted transcript transcriptAgreement : Prop) : Prop :=
  AySCWRConj checkerAccepted (AySCWRConj transcript transcriptAgreement)

def AySCWRFormulaFingerprint
    (originalFingerprint simplificationFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AySCWRConj originalFingerprint
    (AySCWRConj simplificationFingerprint fingerprintAgreement)

def AySCWRBuildEvidence
    (solverBuild simplificationBuild buildAgreement : Prop) : Prop :=
  AySCWRConj solverBuild (AySCWRConj simplificationBuild buildAgreement)

def AySCWRArchiveManifest
    (archiveEntry archiveDigest archiveAgreement : Prop) : Prop :=
  AySCWRConj archiveEntry (AySCWRConj archiveDigest archiveAgreement)

def AySCWRAcceptedReconstruction
    (simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop) : Prop :=
  AySCWRConj simplificationOk
    (AySCWRConj witnessOk
      (AySCWRConj projectionOk
        (AySCWRConj mapOk
          (AySCWRConj digestOk
            (AySCWRConj replayOk
              (AySCWRConj checkerOk
                (AySCWRConj fingerprintOk
                  (AySCWRConj buildOk archiveOk))))))))

def AySCWRPublicSatWitness
    (acceptedReconstruction originalWitness publicSatClaim : Prop) : Prop :=
  AySCWRConj acceptedReconstruction (AySCWRConj originalWitness publicSatClaim)

def AySCWRNoClaimDiagnostic (reason blocksPublication : Prop) : Prop :=
  AySCWRConj reason blocksPublication

def AySCWRRecomputeObligation (reason recomputeRequested : Prop) : Prop :=
  AySCWRConj reason recomputeRequested

theorem ay_scwr_conj_intro {left right : Prop} :
    left -> right -> AySCWRConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_scwr_conj_left {left right : Prop} :
    AySCWRConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_scwr_conj_right {left right : Prop} :
    AySCWRConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_scwr_disj_left {left right : Prop} :
    left -> AySCWRDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_scwr_disj_right {left right : Prop} :
    right -> AySCWRDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_scwr_equisat_intro {source target : Prop} :
    (source -> target) -> (target -> source) -> AySCWREquisat source target :=
  fun forward backward => ay_scwr_conj_intro forward backward

theorem ay_scwr_equisat_forward {source target : Prop} :
    AySCWREquisat source target -> source -> target :=
  fun h => ay_scwr_conj_left h

theorem ay_scwr_equisat_backward {source target : Prop} :
    AySCWREquisat source target -> target -> source :=
  fun h => ay_scwr_conj_right h

theorem ay_scwr_simplification_manifest_intro
    {originalClauses simplifiedClauses simplificationAgreement : Prop} :
    originalClauses -> simplifiedClauses -> simplificationAgreement ->
    AySCWRSimplificationManifest
      originalClauses simplifiedClauses simplificationAgreement :=
  fun horiginal hsimplified hagree =>
    ay_scwr_conj_intro horiginal (ay_scwr_conj_intro hsimplified hagree)

theorem ay_scwr_simplification_manifest_original
    {originalClauses simplifiedClauses simplificationAgreement : Prop} :
    AySCWRSimplificationManifest
      originalClauses simplifiedClauses simplificationAgreement ->
    originalClauses :=
  fun h => ay_scwr_conj_left h

theorem ay_scwr_simplification_manifest_simplified
    {originalClauses simplifiedClauses simplificationAgreement : Prop} :
    AySCWRSimplificationManifest
      originalClauses simplifiedClauses simplificationAgreement ->
    simplifiedClauses :=
  fun h => ay_scwr_conj_left (ay_scwr_conj_right h)

theorem ay_scwr_simplification_manifest_agreement
    {originalClauses simplifiedClauses simplificationAgreement : Prop} :
    AySCWRSimplificationManifest
      originalClauses simplifiedClauses simplificationAgreement ->
    simplificationAgreement :=
  fun h => ay_scwr_conj_right (ay_scwr_conj_right h)

theorem ay_scwr_removed_clause_witness_ledger_intro
    {removedClauses witnessLedger witnessAgreement : Prop} :
    removedClauses -> witnessLedger -> witnessAgreement ->
    AySCWRRemovedClauseWitnessLedger
      removedClauses witnessLedger witnessAgreement :=
  fun hremoved hledger hagree =>
    ay_scwr_conj_intro hremoved (ay_scwr_conj_intro hledger hagree)

theorem ay_scwr_projection_manifest_intro
    {simplifiedWitness originalWitness projectionAgreement : Prop} :
    simplifiedWitness -> originalWitness -> projectionAgreement ->
    AySCWRProjectionManifest
      simplifiedWitness originalWitness projectionAgreement :=
  fun hsimplified horiginal hagree =>
    ay_scwr_conj_intro hsimplified (ay_scwr_conj_intro horiginal hagree)

theorem ay_scwr_dimacs_map_intro
    {internalToDimacs dimacsToInternal mapAgreement : Prop} :
    internalToDimacs -> dimacsToInternal -> mapAgreement ->
    AySCWRDimacsMap internalToDimacs dimacsToInternal mapAgreement :=
  fun hforward hbackward hagree =>
    ay_scwr_conj_intro hforward (ay_scwr_conj_intro hbackward hagree)

theorem ay_scwr_assignment_digest_intro
    {simplifiedDigest originalDigest digestAgreement : Prop} :
    simplifiedDigest -> originalDigest -> digestAgreement ->
    AySCWRAssignmentDigest simplifiedDigest originalDigest digestAgreement :=
  fun hsimplified horiginal hagree =>
    ay_scwr_conj_intro hsimplified (ay_scwr_conj_intro horiginal hagree)

theorem ay_scwr_clause_replay_intro
    {clauseReplay originalEvaluation replayAgreement : Prop} :
    clauseReplay -> originalEvaluation -> replayAgreement ->
    AySCWRClauseReplay clauseReplay originalEvaluation replayAgreement :=
  fun hreplay heval hagree =>
    ay_scwr_conj_intro hreplay (ay_scwr_conj_intro heval hagree)

theorem ay_scwr_checker_transcript_intro
    {checkerAccepted transcript transcriptAgreement : Prop} :
    checkerAccepted -> transcript -> transcriptAgreement ->
    AySCWRCheckerTranscript checkerAccepted transcript transcriptAgreement :=
  fun haccepted htranscript hagree =>
    ay_scwr_conj_intro haccepted (ay_scwr_conj_intro htranscript hagree)

theorem ay_scwr_formula_fingerprint_intro
    {originalFingerprint simplificationFingerprint fingerprintAgreement : Prop} :
    originalFingerprint -> simplificationFingerprint -> fingerprintAgreement ->
    AySCWRFormulaFingerprint
      originalFingerprint simplificationFingerprint fingerprintAgreement :=
  fun horiginal hsimplification hagree =>
    ay_scwr_conj_intro horiginal
      (ay_scwr_conj_intro hsimplification hagree)

theorem ay_scwr_build_evidence_intro
    {solverBuild simplificationBuild buildAgreement : Prop} :
    solverBuild -> simplificationBuild -> buildAgreement ->
    AySCWRBuildEvidence solverBuild simplificationBuild buildAgreement :=
  fun hsolver hsimplification hagree =>
    ay_scwr_conj_intro hsolver (ay_scwr_conj_intro hsimplification hagree)

theorem ay_scwr_archive_manifest_intro
    {archiveEntry archiveDigest archiveAgreement : Prop} :
    archiveEntry -> archiveDigest -> archiveAgreement ->
    AySCWRArchiveManifest archiveEntry archiveDigest archiveAgreement :=
  fun hentry hdigest hagree =>
    ay_scwr_conj_intro hentry (ay_scwr_conj_intro hdigest hagree)

theorem ay_scwr_accepted_reconstruction_intro
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    simplificationOk -> witnessOk -> projectionOk -> mapOk -> digestOk ->
    replayOk -> checkerOk -> fingerprintOk -> buildOk -> archiveOk ->
    AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk mapOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk :=
  fun hsimplification hwitness hprojection hmap hdigest hreplay hchecker
      hfingerprint hbuild harchive =>
    ay_scwr_conj_intro hsimplification
      (ay_scwr_conj_intro hwitness
        (ay_scwr_conj_intro hprojection
          (ay_scwr_conj_intro hmap
            (ay_scwr_conj_intro hdigest
              (ay_scwr_conj_intro hreplay
                (ay_scwr_conj_intro hchecker
                  (ay_scwr_conj_intro hfingerprint
                    (ay_scwr_conj_intro hbuild harchive))))))))

theorem ay_scwr_accepted_reconstruction_simplification
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk mapOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    simplificationOk :=
  fun h => ay_scwr_conj_left h

theorem ay_scwr_accepted_reconstruction_witness
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk mapOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    witnessOk :=
  fun h => ay_scwr_conj_left (ay_scwr_conj_right h)

theorem ay_scwr_accepted_reconstruction_projection
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk mapOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    projectionOk :=
  fun h => ay_scwr_conj_left (ay_scwr_conj_right (ay_scwr_conj_right h))

theorem ay_scwr_accepted_reconstruction_map
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk mapOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    mapOk :=
  fun h =>
    ay_scwr_conj_left
      (ay_scwr_conj_right (ay_scwr_conj_right (ay_scwr_conj_right h)))

theorem ay_scwr_accepted_reconstruction_digest
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk mapOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    digestOk :=
  fun h =>
    ay_scwr_conj_left
      (ay_scwr_conj_right
        (ay_scwr_conj_right (ay_scwr_conj_right (ay_scwr_conj_right h))))

theorem ay_scwr_accepted_reconstruction_replay
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk mapOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    replayOk :=
  fun h =>
    ay_scwr_conj_left
      (ay_scwr_conj_right
        (ay_scwr_conj_right
          (ay_scwr_conj_right (ay_scwr_conj_right
            (ay_scwr_conj_right h)))))

theorem ay_scwr_accepted_reconstruction_checker
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk mapOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    checkerOk :=
  fun h =>
    ay_scwr_conj_left
      (ay_scwr_conj_right
        (ay_scwr_conj_right
          (ay_scwr_conj_right
            (ay_scwr_conj_right (ay_scwr_conj_right
              (ay_scwr_conj_right h))))))

theorem ay_scwr_accepted_reconstruction_fingerprint
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk mapOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    fingerprintOk :=
  fun h =>
    ay_scwr_conj_left
      (ay_scwr_conj_right
        (ay_scwr_conj_right
          (ay_scwr_conj_right
            (ay_scwr_conj_right
              (ay_scwr_conj_right (ay_scwr_conj_right
                (ay_scwr_conj_right h)))))))

theorem ay_scwr_accepted_reconstruction_build
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk mapOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    buildOk :=
  fun h =>
    ay_scwr_conj_left
      (ay_scwr_conj_right
        (ay_scwr_conj_right
          (ay_scwr_conj_right
            (ay_scwr_conj_right
              (ay_scwr_conj_right
                (ay_scwr_conj_right (ay_scwr_conj_right
                  (ay_scwr_conj_right h))))))))

theorem ay_scwr_accepted_reconstruction_archive
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk : Prop} :
    AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk mapOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    archiveOk :=
  fun h =>
    ay_scwr_conj_right
      (ay_scwr_conj_right
        (ay_scwr_conj_right
          (ay_scwr_conj_right
            (ay_scwr_conj_right
              (ay_scwr_conj_right
                (ay_scwr_conj_right (ay_scwr_conj_right
                  (ay_scwr_conj_right h))))))))

theorem ay_scwr_public_sat_witness_intro
    {acceptedReconstruction originalWitness publicSatClaim : Prop} :
    acceptedReconstruction -> originalWitness -> publicSatClaim ->
    AySCWRPublicSatWitness
      acceptedReconstruction originalWitness publicSatClaim :=
  fun hevidence hwitness hclaim =>
    ay_scwr_conj_intro hevidence (ay_scwr_conj_intro hwitness hclaim)

theorem ay_scwr_public_sat_witness_evidence
    {acceptedReconstruction originalWitness publicSatClaim : Prop} :
    AySCWRPublicSatWitness
      acceptedReconstruction originalWitness publicSatClaim ->
    acceptedReconstruction :=
  fun h => ay_scwr_conj_left h

theorem ay_scwr_public_sat_witness_claim
    {acceptedReconstruction originalWitness publicSatClaim : Prop} :
    AySCWRPublicSatWitness
      acceptedReconstruction originalWitness publicSatClaim ->
    publicSatClaim :=
  fun h => ay_scwr_conj_right (ay_scwr_conj_right h)

theorem ay_scwr_accepted_reconstruction_publishes_sound_sat
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk mapOk
      digestOk replayOk checkerOk fingerprintOk buildOk archiveOk ->
    originalWitness -> publicSatClaim ->
    AySCWRPublicSatWitness
      (AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk
        mapOk digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim :=
  ay_scwr_public_sat_witness_intro

theorem ay_scwr_reconstruction_preserves_original_truth
    {simplifiedTruth originalTruth : Prop} :
    AySCWREquisat simplifiedTruth originalTruth -> simplifiedTruth ->
    originalTruth :=
  ay_scwr_equisat_forward

theorem ay_scwr_public_sat_requires_accepted_reconstruction
    {acceptedReconstruction originalWitness publicSatClaim : Prop} :
    AySCWRPublicSatWitness
      acceptedReconstruction originalWitness publicSatClaim ->
    acceptedReconstruction :=
  ay_scwr_public_sat_witness_evidence

theorem ay_scwr_publication_requires_simplification
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySCWRPublicSatWitness
      (AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk
        mapOk digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    simplificationOk :=
  fun h => ay_scwr_accepted_reconstruction_simplification
    (ay_scwr_public_sat_witness_evidence h)

theorem ay_scwr_publication_requires_witness
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySCWRPublicSatWitness
      (AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk
        mapOk digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    witnessOk :=
  fun h => ay_scwr_accepted_reconstruction_witness
    (ay_scwr_public_sat_witness_evidence h)

theorem ay_scwr_publication_requires_projection
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySCWRPublicSatWitness
      (AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk
        mapOk digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    projectionOk :=
  fun h => ay_scwr_accepted_reconstruction_projection
    (ay_scwr_public_sat_witness_evidence h)

theorem ay_scwr_publication_requires_map
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySCWRPublicSatWitness
      (AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk
        mapOk digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    mapOk :=
  fun h => ay_scwr_accepted_reconstruction_map
    (ay_scwr_public_sat_witness_evidence h)

theorem ay_scwr_publication_requires_digest
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySCWRPublicSatWitness
      (AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk
        mapOk digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    digestOk :=
  fun h => ay_scwr_accepted_reconstruction_digest
    (ay_scwr_public_sat_witness_evidence h)

theorem ay_scwr_publication_requires_replay
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySCWRPublicSatWitness
      (AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk
        mapOk digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    replayOk :=
  fun h => ay_scwr_accepted_reconstruction_replay
    (ay_scwr_public_sat_witness_evidence h)

theorem ay_scwr_publication_requires_checker
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySCWRPublicSatWitness
      (AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk
        mapOk digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    checkerOk :=
  fun h => ay_scwr_accepted_reconstruction_checker
    (ay_scwr_public_sat_witness_evidence h)

theorem ay_scwr_publication_requires_fingerprint
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySCWRPublicSatWitness
      (AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk
        mapOk digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    fingerprintOk :=
  fun h => ay_scwr_accepted_reconstruction_fingerprint
    (ay_scwr_public_sat_witness_evidence h)

theorem ay_scwr_publication_requires_build
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySCWRPublicSatWitness
      (AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk
        mapOk digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    buildOk :=
  fun h => ay_scwr_accepted_reconstruction_build
    (ay_scwr_public_sat_witness_evidence h)

theorem ay_scwr_publication_requires_archive
    {simplificationOk witnessOk projectionOk mapOk digestOk replayOk checkerOk
      fingerprintOk buildOk archiveOk originalWitness publicSatClaim : Prop} :
    AySCWRPublicSatWitness
      (AySCWRAcceptedReconstruction simplificationOk witnessOk projectionOk
        mapOk digestOk replayOk checkerOk fingerprintOk buildOk archiveOk)
      originalWitness publicSatClaim ->
    archiveOk :=
  fun h => ay_scwr_accepted_reconstruction_archive
    (ay_scwr_public_sat_witness_evidence h)

theorem ay_scwr_no_claim_diagnostic_intro
    {reason blocksPublication : Prop} :
    reason -> blocksPublication ->
    AySCWRNoClaimDiagnostic reason blocksPublication :=
  ay_scwr_conj_intro

theorem ay_scwr_no_claim_diagnostic_blocks
    {reason blocksPublication : Prop} :
    AySCWRNoClaimDiagnostic reason blocksPublication -> blocksPublication :=
  ay_scwr_conj_right

theorem ay_scwr_recompute_obligation_intro
    {reason recomputeRequested : Prop} :
    reason -> recomputeRequested ->
    AySCWRRecomputeObligation reason recomputeRequested :=
  ay_scwr_conj_intro

theorem ay_scwr_recompute_obligation_request
    {reason recomputeRequested : Prop} :
    AySCWRRecomputeObligation reason recomputeRequested -> recomputeRequested :=
  ay_scwr_conj_right

theorem ay_scwr_simplification_failure_no_claim
    {simplificationFailure blocksPublication : Prop} :
    simplificationFailure -> blocksPublication ->
    AySCWRNoClaimDiagnostic simplificationFailure blocksPublication :=
  ay_scwr_no_claim_diagnostic_intro

theorem ay_scwr_simplification_failure_recompute
    {simplificationFailure recomputeRequested : Prop} :
    simplificationFailure -> recomputeRequested ->
    AySCWRRecomputeObligation simplificationFailure recomputeRequested :=
  ay_scwr_recompute_obligation_intro

theorem ay_scwr_witness_failure_no_claim
    {witnessFailure blocksPublication : Prop} :
    witnessFailure -> blocksPublication ->
    AySCWRNoClaimDiagnostic witnessFailure blocksPublication :=
  ay_scwr_no_claim_diagnostic_intro

theorem ay_scwr_projection_failure_no_claim
    {projectionFailure blocksPublication : Prop} :
    projectionFailure -> blocksPublication ->
    AySCWRNoClaimDiagnostic projectionFailure blocksPublication :=
  ay_scwr_no_claim_diagnostic_intro

theorem ay_scwr_map_failure_no_claim
    {mapFailure blocksPublication : Prop} :
    mapFailure -> blocksPublication ->
    AySCWRNoClaimDiagnostic mapFailure blocksPublication :=
  ay_scwr_no_claim_diagnostic_intro

theorem ay_scwr_digest_failure_no_claim
    {digestFailure blocksPublication : Prop} :
    digestFailure -> blocksPublication ->
    AySCWRNoClaimDiagnostic digestFailure blocksPublication :=
  ay_scwr_no_claim_diagnostic_intro

theorem ay_scwr_replay_failure_no_claim
    {replayFailure blocksPublication : Prop} :
    replayFailure -> blocksPublication ->
    AySCWRNoClaimDiagnostic replayFailure blocksPublication :=
  ay_scwr_no_claim_diagnostic_intro

theorem ay_scwr_checker_failure_no_claim
    {checkerFailure blocksPublication : Prop} :
    checkerFailure -> blocksPublication ->
    AySCWRNoClaimDiagnostic checkerFailure blocksPublication :=
  ay_scwr_no_claim_diagnostic_intro

theorem ay_scwr_fingerprint_failure_no_claim
    {fingerprintFailure blocksPublication : Prop} :
    fingerprintFailure -> blocksPublication ->
    AySCWRNoClaimDiagnostic fingerprintFailure blocksPublication :=
  ay_scwr_no_claim_diagnostic_intro

theorem ay_scwr_build_failure_no_claim
    {buildFailure blocksPublication : Prop} :
    buildFailure -> blocksPublication ->
    AySCWRNoClaimDiagnostic buildFailure blocksPublication :=
  ay_scwr_no_claim_diagnostic_intro

theorem ay_scwr_archive_failure_no_claim
    {archiveFailure blocksPublication : Prop} :
    archiveFailure -> blocksPublication ->
    AySCWRNoClaimDiagnostic archiveFailure blocksPublication :=
  ay_scwr_no_claim_diagnostic_intro

theorem ay_scwr_bad_reconstruction_cannot_bless_sat
    {failure blocksPublication recomputeRequested : Prop} :
    AySCWRNoClaimDiagnostic failure blocksPublication ->
    AySCWRRecomputeObligation failure recomputeRequested ->
    AySCWRConj blocksPublication recomputeRequested :=
  fun hdiagnostic hrecompute =>
    ay_scwr_conj_intro
      (ay_scwr_no_claim_diagnostic_blocks hdiagnostic)
      (ay_scwr_recompute_obligation_request hrecompute)
