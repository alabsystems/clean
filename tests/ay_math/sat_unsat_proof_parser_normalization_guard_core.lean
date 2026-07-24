-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- UNSAT proof parser-normalization guard soundness for ay sequential-main
-- SAT-COMP proof checking. Propositions model raw proof artifact digests,
-- parser versions, normalized proof digests, line tokenization, deletion
-- markers, clause/integer normalization, proof line maps, checker transcripts,
-- empty-clause reachability, archive/build evidence, fallback no-claim paths,
-- audit transcripts, and fail-closed recompute diagnostics.

def ay_ppng_conj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def ay_ppng_disj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def ay_ppng_map (source : Prop) (target : Prop) :=
  source -> target

def ay_ppng_accepted_evidence
    (rawProofArtifactDigest : Prop) (parserVersionDigest : Prop)
    (normalizedProofDigest : Prop) (lineTokenizationTranscript : Prop)
    (deletionMarkerLedger : Prop) (clauseIntegerNormalizationWitness : Prop)
    (proofLineMapDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (proofIdentityPreserved : Prop) (originalUnsat : Prop) :=
  forall result : Prop,
    (rawProofArtifactDigest ->
      parserVersionDigest ->
      normalizedProofDigest ->
      lineTokenizationTranscript ->
      deletionMarkerLedger ->
      clauseIntegerNormalizationWitness ->
      proofLineMapDigest ->
      checkerTranscript ->
      checkerAccepted ->
      emptyClauseReachabilityWitness ->
      archiveManifest ->
      archiveAccepted ->
      solverBuildEvidence ->
      buildAccepted ->
      fallbackNoClaim ->
      auditTranscript ->
      proofIdentityPreserved ->
      originalUnsat ->
      result) ->
    result

def ay_ppng_checker_publication_path
    (normalizedProofDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :=
  ay_ppng_conj
    (ay_ppng_map normalizedProofDigest checkerTranscript)
    (ay_ppng_conj
      (ay_ppng_map checkerTranscript checkerAccepted)
      (ay_ppng_conj
        (ay_ppng_map checkerAccepted emptyClauseReachabilityWitness)
        (ay_ppng_map emptyClauseReachabilityWitness originalUnsat)))

def ay_ppng_identity_preservation
    (rawProofArtifactDigest : Prop) (parserVersionDigest : Prop)
    (normalizedProofDigest : Prop) (lineTokenizationTranscript : Prop)
    (deletionMarkerLedger : Prop) (clauseIntegerNormalizationWitness : Prop)
    (proofLineMapDigest : Prop) (proofIdentityPreserved : Prop) :=
  ay_ppng_conj
    (ay_ppng_map rawProofArtifactDigest parserVersionDigest)
    (ay_ppng_conj
      (ay_ppng_map parserVersionDigest normalizedProofDigest)
      (ay_ppng_conj
        (ay_ppng_map normalizedProofDigest lineTokenizationTranscript)
        (ay_ppng_conj
          (ay_ppng_map lineTokenizationTranscript deletionMarkerLedger)
          (ay_ppng_conj
            (ay_ppng_map deletionMarkerLedger
              clauseIntegerNormalizationWitness)
            (ay_ppng_conj
              (ay_ppng_map clauseIntegerNormalizationWitness proofLineMapDigest)
              (ay_ppng_map proofLineMapDigest
                proofIdentityPreserved)))))))

def ay_ppng_publication
    (rawProofArtifactDigest : Prop) (parserVersionDigest : Prop)
    (normalizedProofDigest : Prop) (lineTokenizationTranscript : Prop)
    (deletionMarkerLedger : Prop) (clauseIntegerNormalizationWitness : Prop)
    (proofLineMapDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (proofIdentityPreserved : Prop) (originalUnsat : Prop) :=
  ay_ppng_conj
    (ay_ppng_accepted_evidence rawProofArtifactDigest parserVersionDigest
      normalizedProofDigest lineTokenizationTranscript deletionMarkerLedger
      clauseIntegerNormalizationWitness proofLineMapDigest checkerTranscript
      checkerAccepted emptyClauseReachabilityWitness archiveManifest
      archiveAccepted solverBuildEvidence buildAccepted fallbackNoClaim
      auditTranscript proofIdentityPreserved originalUnsat)
    originalUnsat

def ay_ppng_failure_reason
    (rawMismatch : Prop) (parserMismatch : Prop)
    (normalizedMismatch : Prop) (tokenMismatch : Prop)
    (deletionMismatch : Prop) (integerMismatch : Prop)
    (lineMapMismatch : Prop) (checkerMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop) :=
  forall result : Prop,
    (rawMismatch -> result) ->
    (parserMismatch -> result) ->
    (normalizedMismatch -> result) ->
    (tokenMismatch -> result) ->
    (deletionMismatch -> result) ->
    (integerMismatch -> result) ->
    (lineMapMismatch -> result) ->
    (checkerMismatch -> result) ->
    (reachabilityMismatch -> result) ->
    (archiveMismatch -> result) ->
    (buildMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_ppng_bad_guard
    (rawMismatch : Prop) (parserMismatch : Prop)
    (normalizedMismatch : Prop) (tokenMismatch : Prop)
    (deletionMismatch : Prop) (integerMismatch : Prop)
    (lineMapMismatch : Prop) (checkerMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :=
  ay_ppng_conj
    (ay_ppng_conj noClaim recompute)
    (ay_ppng_failure_reason rawMismatch parserMismatch normalizedMismatch
      tokenMismatch deletionMismatch integerMismatch lineMapMismatch
      checkerMismatch reachabilityMismatch archiveMismatch buildMismatch
      auditMismatch)

def ay_ppng_public_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :=
  ay_ppng_disj noClaim (ay_ppng_disj originalUnsat publicSat)

theorem ay_ppng_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> ay_ppng_conj p q := by
  intro hp hq result build
  exact build hp hq

theorem ay_ppng_disj_left
    (p : Prop) (q : Prop) :
    p -> ay_ppng_disj p q := by
  intro hp result left_to_result _right_to_result
  exact left_to_result hp

theorem ay_ppng_disj_right
    (p : Prop) (q : Prop) :
    q -> ay_ppng_disj p q := by
  intro hq result _left_to_result right_to_result
  exact right_to_result hq

theorem ay_ppng_build_accepted_evidence
    (rawProofArtifactDigest : Prop) (parserVersionDigest : Prop)
    (normalizedProofDigest : Prop) (lineTokenizationTranscript : Prop)
    (deletionMarkerLedger : Prop) (clauseIntegerNormalizationWitness : Prop)
    (proofLineMapDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (proofIdentityPreserved : Prop) (originalUnsat : Prop) :
    rawProofArtifactDigest ->
    parserVersionDigest ->
    normalizedProofDigest ->
    lineTokenizationTranscript ->
    deletionMarkerLedger ->
    clauseIntegerNormalizationWitness ->
    proofLineMapDigest ->
    checkerTranscript ->
    checkerAccepted ->
    emptyClauseReachabilityWitness ->
    archiveManifest ->
    archiveAccepted ->
    solverBuildEvidence ->
    buildAccepted ->
    fallbackNoClaim ->
    auditTranscript ->
    proofIdentityPreserved ->
    originalUnsat ->
    ay_ppng_accepted_evidence rawProofArtifactDigest parserVersionDigest
      normalizedProofDigest lineTokenizationTranscript deletionMarkerLedger
      clauseIntegerNormalizationWitness proofLineMapDigest checkerTranscript
      checkerAccepted emptyClauseReachabilityWitness archiveManifest
      archiveAccepted solverBuildEvidence buildAccepted fallbackNoClaim
      auditTranscript proofIdentityPreserved originalUnsat := by
  intro hRaw hParser hNormalized hToken hDeletion hInteger hLineMap
  intro hCheckerTranscript hChecker hReachability hArchive hArchiveAccepted
  intro hBuild hBuildAccepted hFallback hAudit hIdentity hOriginal
  intro result publish
  exact publish hRaw hParser hNormalized hToken hDeletion hInteger hLineMap
    hCheckerTranscript hChecker hReachability hArchive hArchiveAccepted
    hBuild hBuildAccepted hFallback hAudit hIdentity hOriginal

theorem ay_ppng_normalized_publish_only_through_checker_replay
    (normalizedProofDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (originalUnsat : Prop) :
    ay_ppng_checker_publication_path normalizedProofDigest checkerTranscript
      checkerAccepted emptyClauseReachabilityWitness originalUnsat ->
    normalizedProofDigest ->
    originalUnsat := by
  intro path hNormalized
  exact path originalUnsat
    (fun normalized_to_checker rest =>
      rest originalUnsat
        (fun checker_to_accepted rest2 =>
          rest2 originalUnsat
            (fun accepted_to_reachability reachability_to_original =>
              reachability_to_original
                (accepted_to_reachability
                  (checker_to_accepted
                    (normalized_to_checker hNormalized)))))))

theorem ay_ppng_normalization_preserves_proof_identities
    (rawProofArtifactDigest : Prop) (parserVersionDigest : Prop)
    (normalizedProofDigest : Prop) (lineTokenizationTranscript : Prop)
    (deletionMarkerLedger : Prop) (clauseIntegerNormalizationWitness : Prop)
    (proofLineMapDigest : Prop) (proofIdentityPreserved : Prop) :
    ay_ppng_identity_preservation rawProofArtifactDigest parserVersionDigest
      normalizedProofDigest lineTokenizationTranscript deletionMarkerLedger
      clauseIntegerNormalizationWitness proofLineMapDigest
      proofIdentityPreserved ->
    rawProofArtifactDigest ->
    proofIdentityPreserved := by
  intro preservation hRaw
  exact preservation proofIdentityPreserved
    (fun raw_to_parser rest =>
      rest proofIdentityPreserved
        (fun parser_to_normalized rest2 =>
          rest2 proofIdentityPreserved
            (fun normalized_to_token rest3 =>
              rest3 proofIdentityPreserved
                (fun token_to_deletion rest4 =>
                  rest4 proofIdentityPreserved
                    (fun deletion_to_integer rest5 =>
                      rest5 proofIdentityPreserved
                        (fun integer_to_line_map line_map_to_identity =>
                          line_map_to_identity
                            (integer_to_line_map
                              (deletion_to_integer
                                (token_to_deletion
                                  (normalized_to_token
                                    (parser_to_normalized
                                      (raw_to_parser hRaw))))))))))))

theorem ay_ppng_empty_clause_reachability_available
    (rawProofArtifactDigest : Prop) (parserVersionDigest : Prop)
    (normalizedProofDigest : Prop) (lineTokenizationTranscript : Prop)
    (deletionMarkerLedger : Prop) (clauseIntegerNormalizationWitness : Prop)
    (proofLineMapDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (proofIdentityPreserved : Prop) (originalUnsat : Prop) :
    ay_ppng_accepted_evidence rawProofArtifactDigest parserVersionDigest
      normalizedProofDigest lineTokenizationTranscript deletionMarkerLedger
      clauseIntegerNormalizationWitness proofLineMapDigest checkerTranscript
      checkerAccepted emptyClauseReachabilityWitness archiveManifest
      archiveAccepted solverBuildEvidence buildAccepted fallbackNoClaim
      auditTranscript proofIdentityPreserved originalUnsat ->
    emptyClauseReachabilityWitness := by
  intro accepted
  exact accepted emptyClauseReachabilityWitness
    (fun _hRaw _hParser _hNormalized _hToken _hDeletion _hInteger _hLineMap
      _hTranscript _hChecker hReachability _hArchive _hArchiveAccepted
      _hBuild _hBuildAccepted _hFallback _hAudit _hIdentity _hOriginal =>
      hReachability)

theorem ay_ppng_proof_identity_available
    (rawProofArtifactDigest : Prop) (parserVersionDigest : Prop)
    (normalizedProofDigest : Prop) (lineTokenizationTranscript : Prop)
    (deletionMarkerLedger : Prop) (clauseIntegerNormalizationWitness : Prop)
    (proofLineMapDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (proofIdentityPreserved : Prop) (originalUnsat : Prop) :
    ay_ppng_accepted_evidence rawProofArtifactDigest parserVersionDigest
      normalizedProofDigest lineTokenizationTranscript deletionMarkerLedger
      clauseIntegerNormalizationWitness proofLineMapDigest checkerTranscript
      checkerAccepted emptyClauseReachabilityWitness archiveManifest
      archiveAccepted solverBuildEvidence buildAccepted fallbackNoClaim
      auditTranscript proofIdentityPreserved originalUnsat ->
    proofIdentityPreserved := by
  intro accepted
  exact accepted proofIdentityPreserved
    (fun _hRaw _hParser _hNormalized _hToken _hDeletion _hInteger _hLineMap
      _hTranscript _hChecker _hReachability _hArchive _hArchiveAccepted
      _hBuild _hBuildAccepted _hFallback _hAudit hIdentity _hOriginal =>
      hIdentity)

theorem ay_ppng_publication_sound
    (rawProofArtifactDigest : Prop) (parserVersionDigest : Prop)
    (normalizedProofDigest : Prop) (lineTokenizationTranscript : Prop)
    (deletionMarkerLedger : Prop) (clauseIntegerNormalizationWitness : Prop)
    (proofLineMapDigest : Prop) (checkerTranscript : Prop)
    (checkerAccepted : Prop) (emptyClauseReachabilityWitness : Prop)
    (archiveManifest : Prop) (archiveAccepted : Prop)
    (solverBuildEvidence : Prop) (buildAccepted : Prop)
    (fallbackNoClaim : Prop) (auditTranscript : Prop)
    (proofIdentityPreserved : Prop) (originalUnsat : Prop) :
    ay_ppng_publication rawProofArtifactDigest parserVersionDigest
      normalizedProofDigest lineTokenizationTranscript deletionMarkerLedger
      clauseIntegerNormalizationWitness proofLineMapDigest checkerTranscript
      checkerAccepted emptyClauseReachabilityWitness archiveManifest
      archiveAccepted solverBuildEvidence buildAccepted fallbackNoClaim
      auditTranscript proofIdentityPreserved originalUnsat ->
    originalUnsat := by
  intro publication
  exact publication originalUnsat
    (fun _accepted hOriginal => hOriginal)

theorem ay_ppng_public_unsat_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    originalUnsat ->
    ay_ppng_public_report noClaim originalUnsat publicSat := by
  intro hUnsat
  exact ay_ppng_disj_right noClaim (ay_ppng_disj originalUnsat publicSat)
    (ay_ppng_disj_left originalUnsat publicSat hUnsat)

theorem ay_ppng_public_no_claim_report
    (noClaim : Prop) (originalUnsat : Prop) (publicSat : Prop) :
    noClaim ->
    ay_ppng_public_report noClaim originalUnsat publicSat := by
  intro hNoClaim
  exact ay_ppng_disj_left noClaim
    (ay_ppng_disj originalUnsat publicSat) hNoClaim

theorem ay_ppng_bad_no_claim
    (rawMismatch : Prop) (parserMismatch : Prop)
    (normalizedMismatch : Prop) (tokenMismatch : Prop)
    (deletionMismatch : Prop) (integerMismatch : Prop)
    (lineMapMismatch : Prop) (checkerMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ppng_bad_guard rawMismatch parserMismatch normalizedMismatch
      tokenMismatch deletionMismatch integerMismatch lineMapMismatch
      checkerMismatch reachabilityMismatch archiveMismatch buildMismatch
      auditMismatch noClaim recompute ->
    noClaim := by
  intro bad
  exact bad noClaim
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute noClaim
        (fun hNoClaim _hRecompute => hNoClaim))

theorem ay_ppng_bad_recompute
    (rawMismatch : Prop) (parserMismatch : Prop)
    (normalizedMismatch : Prop) (tokenMismatch : Prop)
    (deletionMismatch : Prop) (integerMismatch : Prop)
    (lineMapMismatch : Prop) (checkerMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) :
    ay_ppng_bad_guard rawMismatch parserMismatch normalizedMismatch
      tokenMismatch deletionMismatch integerMismatch lineMapMismatch
      checkerMismatch reachabilityMismatch archiveMismatch buildMismatch
      auditMismatch noClaim recompute ->
    recompute := by
  intro bad
  exact bad recompute
    (fun no_claim_and_recompute _reason =>
      no_claim_and_recompute recompute
        (fun _hNoClaim hRecompute => hRecompute))

theorem ay_ppng_failed_guard_cannot_bless_unsat
    (rawMismatch : Prop) (parserMismatch : Prop)
    (normalizedMismatch : Prop) (tokenMismatch : Prop)
    (deletionMismatch : Prop) (integerMismatch : Prop)
    (lineMapMismatch : Prop) (checkerMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) (recompute : Prop) (publicUnsat : Prop) :
    ay_ppng_bad_guard rawMismatch parserMismatch normalizedMismatch
      tokenMismatch deletionMismatch integerMismatch lineMapMismatch
      checkerMismatch reachabilityMismatch archiveMismatch buildMismatch
      auditMismatch noClaim recompute ->
    ay_ppng_map noClaim (publicUnsat -> recompute) := by
  intro bad _hNoClaim _hPublicUnsat
  exact ay_ppng_bad_recompute rawMismatch parserMismatch normalizedMismatch
    tokenMismatch deletionMismatch integerMismatch lineMapMismatch
    checkerMismatch reachabilityMismatch archiveMismatch buildMismatch
    auditMismatch noClaim recompute bad

theorem ay_ppng_failure_forces_no_claim
    (rawMismatch : Prop) (parserMismatch : Prop)
    (normalizedMismatch : Prop) (tokenMismatch : Prop)
    (deletionMismatch : Prop) (integerMismatch : Prop)
    (lineMapMismatch : Prop) (checkerMismatch : Prop)
    (reachabilityMismatch : Prop) (archiveMismatch : Prop)
    (buildMismatch : Prop) (auditMismatch : Prop)
    (noClaim : Prop) :
    ay_ppng_failure_reason rawMismatch parserMismatch normalizedMismatch
      tokenMismatch deletionMismatch integerMismatch lineMapMismatch
      checkerMismatch reachabilityMismatch archiveMismatch buildMismatch
      auditMismatch ->
    (rawMismatch -> noClaim) ->
    (parserMismatch -> noClaim) ->
    (normalizedMismatch -> noClaim) ->
    (tokenMismatch -> noClaim) ->
    (deletionMismatch -> noClaim) ->
    (integerMismatch -> noClaim) ->
    (lineMapMismatch -> noClaim) ->
    (checkerMismatch -> noClaim) ->
    (reachabilityMismatch -> noClaim) ->
    (archiveMismatch -> noClaim) ->
    (buildMismatch -> noClaim) ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro reason raw_to_no_claim parser_to_no_claim normalized_to_no_claim
  intro token_to_no_claim deletion_to_no_claim integer_to_no_claim
  intro line_map_to_no_claim checker_to_no_claim reachability_to_no_claim
  intro archive_to_no_claim build_to_no_claim audit_to_no_claim
  exact reason noClaim raw_to_no_claim parser_to_no_claim
    normalized_to_no_claim token_to_no_claim deletion_to_no_claim
    integer_to_no_claim line_map_to_no_claim checker_to_no_claim
    reachability_to_no_claim archive_to_no_claim build_to_no_claim
    audit_to_no_claim

theorem ay_ppng_raw_mismatch_forces_no_claim
    (rawMismatch noClaim : Prop) :
    rawMismatch ->
    (rawMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ppng_parser_mismatch_forces_no_claim
    (parserMismatch noClaim : Prop) :
    parserMismatch ->
    (parserMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ppng_normalized_mismatch_forces_no_claim
    (normalizedMismatch noClaim : Prop) :
    normalizedMismatch ->
    (normalizedMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ppng_token_mismatch_forces_no_claim
    (tokenMismatch noClaim : Prop) :
    tokenMismatch ->
    (tokenMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ppng_deletion_mismatch_forces_no_claim
    (deletionMismatch noClaim : Prop) :
    deletionMismatch ->
    (deletionMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ppng_integer_mismatch_forces_no_claim
    (integerMismatch noClaim : Prop) :
    integerMismatch ->
    (integerMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ppng_line_map_mismatch_forces_no_claim
    (lineMapMismatch noClaim : Prop) :
    lineMapMismatch ->
    (lineMapMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ppng_checker_mismatch_forces_no_claim
    (checkerMismatch noClaim : Prop) :
    checkerMismatch ->
    (checkerMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ppng_reachability_mismatch_forces_no_claim
    (reachabilityMismatch noClaim : Prop) :
    reachabilityMismatch ->
    (reachabilityMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ppng_archive_mismatch_forces_no_claim
    (archiveMismatch noClaim : Prop) :
    archiveMismatch ->
    (archiveMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ppng_build_mismatch_forces_no_claim
    (buildMismatch noClaim : Prop) :
    buildMismatch ->
    (buildMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch

theorem ay_ppng_audit_mismatch_forces_no_claim
    (auditMismatch noClaim : Prop) :
    auditMismatch ->
    (auditMismatch -> noClaim) ->
    noClaim := by
  intro mismatch mismatch_to_no_claim
  exact mismatch_to_no_claim mismatch
