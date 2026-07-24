-- SAT-COMP validator public exit-code consistency core.
--
-- Public reporting is sound only when exit code, public result kind,
-- certificate digest, checker transcript, solver build evidence, original
-- formula fingerprint, and no-claim/recompute branch are mutually consistent.

def ay_vpec_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vpec_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vpec_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vpec_disj satFact (ay_vpec_disj unsatFact noClaimFact)

def ay_vpec_consistency
    (exitCode publicResultKind certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint fallbackBranch : Prop) :
    Prop :=
  ay_vpec_conj exitCode
    (ay_vpec_conj publicResultKind
      (ay_vpec_conj certificateDigest
        (ay_vpec_conj checkerTranscript
          (ay_vpec_conj solverBuildEvidence
            (ay_vpec_conj originalFormulaFingerprint fallbackBranch)))))

def ay_vpec_sat_exit
    (consistency acceptedModelProvenance originalModel : Prop) : Prop :=
  ay_vpec_conj consistency
    (ay_vpec_conj acceptedModelProvenance originalModel)

def ay_vpec_unsat_exit
    (consistency acceptedProofProvenance originalEmptyClause : Prop) : Prop :=
  ay_vpec_conj consistency
    (ay_vpec_conj acceptedProofProvenance originalEmptyClause)

def ay_vpec_no_claim_exit
    (consistency diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vpec_conj consistency
    (ay_vpec_conj diagnostic noSemanticClaim)

def ay_vpec_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vpec_conj reason
    (ay_vpec_conj (satFact -> False) (unsatFact -> False))

def ay_vpec_recompute
    (reason fallbackBranch fallbackPath : Prop) : Prop :=
  ay_vpec_conj reason (ay_vpec_conj fallbackBranch fallbackPath)

def ay_vpec_inconsistent_exit
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) : Prop :=
  ay_vpec_conj
    (ay_vpec_blocked_publication satFact unsatFact reason)
    (ay_vpec_recompute reason fallbackBranch fallbackPath)

theorem ay_vpec_conj_intro (left right : Prop) :
    left -> right -> ay_vpec_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vpec_conj_left (left right : Prop) :
    ay_vpec_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vpec_conj_right (left right : Prop) :
    ay_vpec_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vpec_disj_left (left right : Prop) :
    left -> ay_vpec_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vpec_disj_right (left right : Prop) :
    right -> ay_vpec_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vpec_consistency_intro
    (exitCode publicResultKind certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint fallbackBranch : Prop) :
    exitCode -> publicResultKind -> certificateDigest ->
    checkerTranscript -> solverBuildEvidence -> originalFormulaFingerprint ->
    fallbackBranch ->
    ay_vpec_consistency exitCode publicResultKind certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      fallbackBranch :=
  fun exitProof kindProof digestProof transcriptProof buildProof
      fingerprintProof fallbackProof =>
    ay_vpec_conj_intro exitCode
      (ay_vpec_conj publicResultKind
        (ay_vpec_conj certificateDigest
          (ay_vpec_conj checkerTranscript
            (ay_vpec_conj solverBuildEvidence
              (ay_vpec_conj originalFormulaFingerprint fallbackBranch)))))
      exitProof
      (ay_vpec_conj_intro publicResultKind
        (ay_vpec_conj certificateDigest
          (ay_vpec_conj checkerTranscript
            (ay_vpec_conj solverBuildEvidence
              (ay_vpec_conj originalFormulaFingerprint fallbackBranch))))
        kindProof
        (ay_vpec_conj_intro certificateDigest
          (ay_vpec_conj checkerTranscript
            (ay_vpec_conj solverBuildEvidence
              (ay_vpec_conj originalFormulaFingerprint fallbackBranch)))
          digestProof
          (ay_vpec_conj_intro checkerTranscript
            (ay_vpec_conj solverBuildEvidence
              (ay_vpec_conj originalFormulaFingerprint fallbackBranch))
            transcriptProof
            (ay_vpec_conj_intro solverBuildEvidence
              (ay_vpec_conj originalFormulaFingerprint fallbackBranch)
              buildProof
              (ay_vpec_conj_intro originalFormulaFingerprint fallbackBranch
                fingerprintProof fallbackProof)))))

theorem ay_vpec_consistency_exit
    (exitCode publicResultKind certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint fallbackBranch : Prop) :
    ay_vpec_consistency exitCode publicResultKind certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      fallbackBranch ->
    exitCode :=
  fun consistency =>
    ay_vpec_conj_left exitCode
      (ay_vpec_conj publicResultKind
        (ay_vpec_conj certificateDigest
          (ay_vpec_conj checkerTranscript
            (ay_vpec_conj solverBuildEvidence
              (ay_vpec_conj originalFormulaFingerprint fallbackBranch)))))
      consistency

theorem ay_vpec_consistency_kind
    (exitCode publicResultKind certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint fallbackBranch : Prop) :
    ay_vpec_consistency exitCode publicResultKind certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      fallbackBranch ->
    publicResultKind :=
  fun consistency =>
    ay_vpec_conj_right exitCode
      (ay_vpec_conj publicResultKind
        (ay_vpec_conj certificateDigest
          (ay_vpec_conj checkerTranscript
            (ay_vpec_conj solverBuildEvidence
              (ay_vpec_conj originalFormulaFingerprint fallbackBranch)))))
      consistency publicResultKind
      (fun kindProof _tail => kindProof)

theorem ay_vpec_consistency_digest
    (exitCode publicResultKind certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint fallbackBranch : Prop) :
    ay_vpec_consistency exitCode publicResultKind certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      fallbackBranch ->
    certificateDigest :=
  fun consistency =>
    ay_vpec_conj_right exitCode
      (ay_vpec_conj publicResultKind
        (ay_vpec_conj certificateDigest
          (ay_vpec_conj checkerTranscript
            (ay_vpec_conj solverBuildEvidence
              (ay_vpec_conj originalFormulaFingerprint fallbackBranch)))))
      consistency certificateDigest
      (fun _kindProof tail =>
        tail certificateDigest (fun digestProof _tail2 => digestProof))

theorem ay_vpec_consistency_transcript
    (exitCode publicResultKind certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint fallbackBranch : Prop) :
    ay_vpec_consistency exitCode publicResultKind certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      fallbackBranch ->
    checkerTranscript :=
  fun consistency =>
    ay_vpec_conj_right exitCode
      (ay_vpec_conj publicResultKind
        (ay_vpec_conj certificateDigest
          (ay_vpec_conj checkerTranscript
            (ay_vpec_conj solverBuildEvidence
              (ay_vpec_conj originalFormulaFingerprint fallbackBranch)))))
      consistency checkerTranscript
      (fun _kindProof tail =>
        tail checkerTranscript
          (fun _digestProof tail2 =>
            tail2 checkerTranscript
              (fun transcriptProof _tail3 => transcriptProof)))

theorem ay_vpec_consistency_build
    (exitCode publicResultKind certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint fallbackBranch : Prop) :
    ay_vpec_consistency exitCode publicResultKind certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      fallbackBranch ->
    solverBuildEvidence :=
  fun consistency =>
    ay_vpec_conj_right exitCode
      (ay_vpec_conj publicResultKind
        (ay_vpec_conj certificateDigest
          (ay_vpec_conj checkerTranscript
            (ay_vpec_conj solverBuildEvidence
              (ay_vpec_conj originalFormulaFingerprint fallbackBranch)))))
      consistency solverBuildEvidence
      (fun _kindProof tail =>
        tail solverBuildEvidence
          (fun _digestProof tail2 =>
            tail2 solverBuildEvidence
              (fun _transcriptProof tail3 =>
                tail3 solverBuildEvidence
                  (fun buildProof _tail4 => buildProof))))

theorem ay_vpec_consistency_fingerprint
    (exitCode publicResultKind certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint fallbackBranch : Prop) :
    ay_vpec_consistency exitCode publicResultKind certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      fallbackBranch ->
    originalFormulaFingerprint :=
  fun consistency =>
    ay_vpec_conj_right exitCode
      (ay_vpec_conj publicResultKind
        (ay_vpec_conj certificateDigest
          (ay_vpec_conj checkerTranscript
            (ay_vpec_conj solverBuildEvidence
              (ay_vpec_conj originalFormulaFingerprint fallbackBranch)))))
      consistency originalFormulaFingerprint
      (fun _kindProof tail =>
        tail originalFormulaFingerprint
          (fun _digestProof tail2 =>
            tail2 originalFormulaFingerprint
              (fun _transcriptProof tail3 =>
                tail3 originalFormulaFingerprint
                  (fun _buildProof tail4 =>
                    tail4 originalFormulaFingerprint
                      (fun fingerprintProof _fallbackProof =>
                        fingerprintProof)))))

theorem ay_vpec_consistency_fallback
    (exitCode publicResultKind certificateDigest checkerTranscript
      solverBuildEvidence originalFormulaFingerprint fallbackBranch : Prop) :
    ay_vpec_consistency exitCode publicResultKind certificateDigest
      checkerTranscript solverBuildEvidence originalFormulaFingerprint
      fallbackBranch ->
    fallbackBranch :=
  fun consistency =>
    ay_vpec_conj_right exitCode
      (ay_vpec_conj publicResultKind
        (ay_vpec_conj certificateDigest
          (ay_vpec_conj checkerTranscript
            (ay_vpec_conj solverBuildEvidence
              (ay_vpec_conj originalFormulaFingerprint fallbackBranch)))))
      consistency fallbackBranch
      (fun _kindProof tail =>
        tail fallbackBranch
          (fun _digestProof tail2 =>
            tail2 fallbackBranch
              (fun _transcriptProof tail3 =>
                tail3 fallbackBranch
                  (fun _buildProof tail4 =>
                    tail4 fallbackBranch
                      (fun _fingerprintProof fallbackProof =>
                        fallbackProof)))))

theorem ay_vpec_sat_exit_intro
    (consistency acceptedModelProvenance originalModel : Prop) :
    consistency -> acceptedModelProvenance -> originalModel ->
    ay_vpec_sat_exit consistency acceptedModelProvenance originalModel :=
  fun consistencyProof provenanceProof modelProof =>
    ay_vpec_conj_intro consistency
      (ay_vpec_conj acceptedModelProvenance originalModel)
      consistencyProof
      (ay_vpec_conj_intro acceptedModelProvenance originalModel
        provenanceProof modelProof)

theorem ay_vpec_sat_exit_consistency
    (consistency acceptedModelProvenance originalModel : Prop) :
    ay_vpec_sat_exit consistency acceptedModelProvenance originalModel ->
    consistency :=
  fun exit =>
    ay_vpec_conj_left consistency
      (ay_vpec_conj acceptedModelProvenance originalModel) exit

theorem ay_vpec_sat_exit_requires_model_provenance
    (consistency acceptedModelProvenance originalModel : Prop) :
    ay_vpec_sat_exit consistency acceptedModelProvenance originalModel ->
    acceptedModelProvenance :=
  fun exit =>
    ay_vpec_conj_right consistency
      (ay_vpec_conj acceptedModelProvenance originalModel)
      exit acceptedModelProvenance
      (fun provenanceProof _modelProof => provenanceProof)

theorem ay_vpec_sat_exit_original_model
    (consistency acceptedModelProvenance originalModel : Prop) :
    ay_vpec_sat_exit consistency acceptedModelProvenance originalModel ->
    originalModel :=
  fun exit =>
    ay_vpec_conj_right consistency
      (ay_vpec_conj acceptedModelProvenance originalModel)
      exit originalModel
      (fun _provenanceProof modelProof => modelProof)

theorem ay_vpec_unsat_exit_intro
    (consistency acceptedProofProvenance originalEmptyClause : Prop) :
    consistency -> acceptedProofProvenance -> originalEmptyClause ->
    ay_vpec_unsat_exit consistency acceptedProofProvenance
      originalEmptyClause :=
  fun consistencyProof provenanceProof proofProof =>
    ay_vpec_conj_intro consistency
      (ay_vpec_conj acceptedProofProvenance originalEmptyClause)
      consistencyProof
      (ay_vpec_conj_intro acceptedProofProvenance originalEmptyClause
        provenanceProof proofProof)

theorem ay_vpec_unsat_exit_consistency
    (consistency acceptedProofProvenance originalEmptyClause : Prop) :
    ay_vpec_unsat_exit consistency acceptedProofProvenance
      originalEmptyClause ->
    consistency :=
  fun exit =>
    ay_vpec_conj_left consistency
      (ay_vpec_conj acceptedProofProvenance originalEmptyClause) exit

theorem ay_vpec_unsat_exit_requires_proof_provenance
    (consistency acceptedProofProvenance originalEmptyClause : Prop) :
    ay_vpec_unsat_exit consistency acceptedProofProvenance
      originalEmptyClause ->
    acceptedProofProvenance :=
  fun exit =>
    ay_vpec_conj_right consistency
      (ay_vpec_conj acceptedProofProvenance originalEmptyClause)
      exit acceptedProofProvenance
      (fun provenanceProof _proofProof => provenanceProof)

theorem ay_vpec_unsat_exit_original_empty_clause
    (consistency acceptedProofProvenance originalEmptyClause : Prop) :
    ay_vpec_unsat_exit consistency acceptedProofProvenance
      originalEmptyClause ->
    originalEmptyClause :=
  fun exit =>
    ay_vpec_conj_right consistency
      (ay_vpec_conj acceptedProofProvenance originalEmptyClause)
      exit originalEmptyClause
      (fun _provenanceProof proofProof => proofProof)

theorem ay_vpec_no_claim_exit_intro
    (consistency diagnostic noSemanticClaim : Prop) :
    consistency -> diagnostic -> noSemanticClaim ->
    ay_vpec_no_claim_exit consistency diagnostic noSemanticClaim :=
  fun consistencyProof diagnosticProof noClaimProof =>
    ay_vpec_conj_intro consistency
      (ay_vpec_conj diagnostic noSemanticClaim)
      consistencyProof
      (ay_vpec_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vpec_no_claim_exit_no_semantic_claim
    (consistency diagnostic noSemanticClaim : Prop) :
    ay_vpec_no_claim_exit consistency diagnostic noSemanticClaim ->
    noSemanticClaim :=
  fun exit =>
    ay_vpec_conj_right consistency
      (ay_vpec_conj diagnostic noSemanticClaim)
      exit noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vpec_accepted_sat_exit_public_sound
    (consistency acceptedModelProvenance originalModel unsatFact noClaimFact :
      Prop) :
    ay_vpec_sat_exit consistency acceptedModelProvenance originalModel ->
    ay_vpec_public_result originalModel unsatFact noClaimFact :=
  fun exit =>
    ay_vpec_disj_left originalModel
      (ay_vpec_disj unsatFact noClaimFact)
      (ay_vpec_sat_exit_original_model consistency acceptedModelProvenance
        originalModel exit)

theorem ay_vpec_accepted_unsat_exit_public_sound
    (satFact consistency acceptedProofProvenance originalEmptyClause
      noClaimFact : Prop) :
    ay_vpec_unsat_exit consistency acceptedProofProvenance
      originalEmptyClause ->
    ay_vpec_public_result satFact originalEmptyClause noClaimFact :=
  fun exit =>
    ay_vpec_disj_right satFact
      (ay_vpec_disj originalEmptyClause noClaimFact)
      (ay_vpec_disj_left originalEmptyClause noClaimFact
        (ay_vpec_unsat_exit_original_empty_clause consistency
          acceptedProofProvenance originalEmptyClause exit))

theorem ay_vpec_no_claim_exit_public_no_claim
    (satFact unsatFact consistency diagnostic noSemanticClaim : Prop) :
    ay_vpec_no_claim_exit consistency diagnostic noSemanticClaim ->
    ay_vpec_public_result satFact unsatFact noSemanticClaim :=
  fun exit =>
    ay_vpec_disj_right satFact
      (ay_vpec_disj unsatFact noSemanticClaim)
      (ay_vpec_disj_right unsatFact noSemanticClaim
        (ay_vpec_no_claim_exit_no_semantic_claim consistency diagnostic
          noSemanticClaim exit))

theorem ay_vpec_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vpec_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vpec_conj_intro reason
      (ay_vpec_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vpec_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vpec_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vpec_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vpec_conj_right reason
      (ay_vpec_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vpec_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vpec_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vpec_conj_right reason
      (ay_vpec_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vpec_recompute_intro
    (reason fallbackBranch fallbackPath : Prop) :
    reason -> fallbackBranch -> fallbackPath ->
    ay_vpec_recompute reason fallbackBranch fallbackPath :=
  fun reasonProof fallbackProof pathProof =>
    ay_vpec_conj_intro reason
      (ay_vpec_conj fallbackBranch fallbackPath)
      reasonProof
      (ay_vpec_conj_intro fallbackBranch fallbackPath fallbackProof
        pathProof)

theorem ay_vpec_inconsistent_exit_intro
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) :
    ay_vpec_blocked_publication satFact unsatFact reason ->
    ay_vpec_recompute reason fallbackBranch fallbackPath ->
    ay_vpec_inconsistent_exit satFact unsatFact reason fallbackBranch
      fallbackPath :=
  fun blocked recompute =>
    ay_vpec_conj_intro
      (ay_vpec_blocked_publication satFact unsatFact reason)
      (ay_vpec_recompute reason fallbackBranch fallbackPath)
      blocked recompute

theorem ay_vpec_inconsistent_exit_blocks_sat
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) :
    ay_vpec_inconsistent_exit satFact unsatFact reason fallbackBranch
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vpec_blocked_publication_no_sat satFact unsatFact reason
      (ay_vpec_conj_left
        (ay_vpec_blocked_publication satFact unsatFact reason)
        (ay_vpec_recompute reason fallbackBranch fallbackPath)
        failure)

theorem ay_vpec_inconsistent_exit_blocks_unsat
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) :
    ay_vpec_inconsistent_exit satFact unsatFact reason fallbackBranch
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vpec_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vpec_conj_left
        (ay_vpec_blocked_publication satFact unsatFact reason)
        (ay_vpec_recompute reason fallbackBranch fallbackPath)
        failure)

theorem ay_vpec_inconsistent_exit_recompute
    (satFact unsatFact reason fallbackBranch fallbackPath : Prop) :
    ay_vpec_inconsistent_exit satFact unsatFact reason fallbackBranch
      fallbackPath ->
    ay_vpec_recompute reason fallbackBranch fallbackPath :=
  fun failure =>
    ay_vpec_conj_right
      (ay_vpec_blocked_publication satFact unsatFact reason)
      (ay_vpec_recompute reason fallbackBranch fallbackPath)
      failure

theorem ay_vpec_inconsistent_exit_result_forces_no_claim
    (satFact unsatFact inconsistentResult fallbackBranch fallbackPath :
      Prop) :
    inconsistentResult -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> fallbackPath ->
    ay_vpec_inconsistent_exit satFact unsatFact inconsistentResult
      fallbackBranch fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vpec_inconsistent_exit_intro satFact unsatFact inconsistentResult
      fallbackBranch fallbackPath
      (ay_vpec_blocked_publication_intro satFact unsatFact
        inconsistentResult reasonProof blockSat blockUnsat)
      (ay_vpec_recompute_intro inconsistentResult fallbackBranch
        fallbackPath reasonProof fallbackProof pathProof)

theorem ay_vpec_inconsistent_certificate_forces_no_claim
    (satFact unsatFact inconsistentCertificate fallbackBranch fallbackPath :
      Prop) :
    inconsistentCertificate -> (satFact -> False) ->
    (unsatFact -> False) -> fallbackBranch -> fallbackPath ->
    ay_vpec_inconsistent_exit satFact unsatFact inconsistentCertificate
      fallbackBranch fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vpec_inconsistent_exit_intro satFact unsatFact
      inconsistentCertificate fallbackBranch fallbackPath
      (ay_vpec_blocked_publication_intro satFact unsatFact
        inconsistentCertificate reasonProof blockSat blockUnsat)
      (ay_vpec_recompute_intro inconsistentCertificate fallbackBranch
        fallbackPath reasonProof fallbackProof pathProof)

theorem ay_vpec_stale_exit_code_cannot_bless_sat
    (satFact unsatFact staleExit fallbackBranch fallbackPath : Prop) :
    ay_vpec_inconsistent_exit satFact unsatFact staleExit fallbackBranch
      fallbackPath ->
    satFact -> False :=
  ay_vpec_inconsistent_exit_blocks_sat satFact unsatFact staleExit
    fallbackBranch fallbackPath

theorem ay_vpec_stale_exit_code_cannot_bless_unsat
    (satFact unsatFact staleExit fallbackBranch fallbackPath : Prop) :
    ay_vpec_inconsistent_exit satFact unsatFact staleExit fallbackBranch
      fallbackPath ->
    unsatFact -> False :=
  ay_vpec_inconsistent_exit_blocks_unsat satFact unsatFact staleExit
    fallbackBranch fallbackPath
