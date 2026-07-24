-- SAT-COMP validator certificate digest provenance core.
--
-- SAT model certificates and UNSAT proof certificates must be tied to a
-- certificate digest, original formula fingerprint, solver build evidence,
-- checker replay transcript, reconstruction mapping, and fallback/no-claim
-- branch before they can justify public SAT/UNSAT results.

def ay_vcdp_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vcdp_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vcdp_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vcdp_disj satFact (ay_vcdp_disj unsatFact noClaimFact)

def ay_vcdp_provenance
    (certificateDigest originalFormulaFingerprint solverBuildEvidence
      checkerReplayTranscript reconstructionMapping fallbackNoClaim :
      Prop) : Prop :=
  ay_vcdp_conj certificateDigest
    (ay_vcdp_conj originalFormulaFingerprint
      (ay_vcdp_conj solverBuildEvidence
        (ay_vcdp_conj checkerReplayTranscript
          (ay_vcdp_conj reconstructionMapping fallbackNoClaim))))

def ay_vcdp_sat_certificate
    (provenance modelCertificate originalModel : Prop) : Prop :=
  ay_vcdp_conj provenance
    (ay_vcdp_conj modelCertificate originalModel)

def ay_vcdp_unsat_certificate
    (provenance proofCertificate originalEmptyClause : Prop) : Prop :=
  ay_vcdp_conj provenance
    (ay_vcdp_conj proofCertificate originalEmptyClause)

def ay_vcdp_no_claim
    (provenance diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vcdp_conj provenance
    (ay_vcdp_conj diagnostic noSemanticClaim)

def ay_vcdp_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vcdp_conj reason
    (ay_vcdp_conj (satFact -> False) (unsatFact -> False))

def ay_vcdp_recompute
    (reason fallbackNoClaim fallbackPath : Prop) : Prop :=
  ay_vcdp_conj reason (ay_vcdp_conj fallbackNoClaim fallbackPath)

def ay_vcdp_provenance_failure
    (satFact unsatFact reason fallbackNoClaim fallbackPath : Prop) : Prop :=
  ay_vcdp_conj
    (ay_vcdp_blocked_publication satFact unsatFact reason)
    (ay_vcdp_recompute reason fallbackNoClaim fallbackPath)

theorem ay_vcdp_conj_intro (left right : Prop) :
    left -> right -> ay_vcdp_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vcdp_conj_left (left right : Prop) :
    ay_vcdp_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vcdp_conj_right (left right : Prop) :
    ay_vcdp_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vcdp_disj_left (left right : Prop) :
    left -> ay_vcdp_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vcdp_disj_right (left right : Prop) :
    right -> ay_vcdp_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vcdp_provenance_intro
    (certificateDigest originalFormulaFingerprint solverBuildEvidence
      checkerReplayTranscript reconstructionMapping fallbackNoClaim :
      Prop) :
    certificateDigest -> originalFormulaFingerprint -> solverBuildEvidence ->
    checkerReplayTranscript -> reconstructionMapping -> fallbackNoClaim ->
    ay_vcdp_provenance certificateDigest originalFormulaFingerprint
      solverBuildEvidence checkerReplayTranscript reconstructionMapping
      fallbackNoClaim :=
  fun digestProof fingerprintProof buildProof replayProof reconstructionProof
      fallbackProof =>
    ay_vcdp_conj_intro certificateDigest
      (ay_vcdp_conj originalFormulaFingerprint
        (ay_vcdp_conj solverBuildEvidence
          (ay_vcdp_conj checkerReplayTranscript
            (ay_vcdp_conj reconstructionMapping fallbackNoClaim))))
      digestProof
      (ay_vcdp_conj_intro originalFormulaFingerprint
        (ay_vcdp_conj solverBuildEvidence
          (ay_vcdp_conj checkerReplayTranscript
            (ay_vcdp_conj reconstructionMapping fallbackNoClaim)))
        fingerprintProof
        (ay_vcdp_conj_intro solverBuildEvidence
          (ay_vcdp_conj checkerReplayTranscript
            (ay_vcdp_conj reconstructionMapping fallbackNoClaim))
          buildProof
          (ay_vcdp_conj_intro checkerReplayTranscript
            (ay_vcdp_conj reconstructionMapping fallbackNoClaim)
            replayProof
            (ay_vcdp_conj_intro reconstructionMapping fallbackNoClaim
              reconstructionProof fallbackProof))))

theorem ay_vcdp_provenance_digest
    (certificateDigest originalFormulaFingerprint solverBuildEvidence
      checkerReplayTranscript reconstructionMapping fallbackNoClaim :
      Prop) :
    ay_vcdp_provenance certificateDigest originalFormulaFingerprint
      solverBuildEvidence checkerReplayTranscript reconstructionMapping
      fallbackNoClaim ->
    certificateDigest :=
  fun provenance =>
    ay_vcdp_conj_left certificateDigest
      (ay_vcdp_conj originalFormulaFingerprint
        (ay_vcdp_conj solverBuildEvidence
          (ay_vcdp_conj checkerReplayTranscript
            (ay_vcdp_conj reconstructionMapping fallbackNoClaim))))
      provenance

theorem ay_vcdp_provenance_fingerprint
    (certificateDigest originalFormulaFingerprint solverBuildEvidence
      checkerReplayTranscript reconstructionMapping fallbackNoClaim :
      Prop) :
    ay_vcdp_provenance certificateDigest originalFormulaFingerprint
      solverBuildEvidence checkerReplayTranscript reconstructionMapping
      fallbackNoClaim ->
    originalFormulaFingerprint :=
  fun provenance =>
    ay_vcdp_conj_right certificateDigest
      (ay_vcdp_conj originalFormulaFingerprint
        (ay_vcdp_conj solverBuildEvidence
          (ay_vcdp_conj checkerReplayTranscript
            (ay_vcdp_conj reconstructionMapping fallbackNoClaim))))
      provenance originalFormulaFingerprint
      (fun fingerprintProof _tail => fingerprintProof)

theorem ay_vcdp_provenance_build
    (certificateDigest originalFormulaFingerprint solverBuildEvidence
      checkerReplayTranscript reconstructionMapping fallbackNoClaim :
      Prop) :
    ay_vcdp_provenance certificateDigest originalFormulaFingerprint
      solverBuildEvidence checkerReplayTranscript reconstructionMapping
      fallbackNoClaim ->
    solverBuildEvidence :=
  fun provenance =>
    ay_vcdp_conj_right certificateDigest
      (ay_vcdp_conj originalFormulaFingerprint
        (ay_vcdp_conj solverBuildEvidence
          (ay_vcdp_conj checkerReplayTranscript
            (ay_vcdp_conj reconstructionMapping fallbackNoClaim))))
      provenance solverBuildEvidence
      (fun _fingerprintProof tail =>
        tail solverBuildEvidence (fun buildProof _tail2 => buildProof))

theorem ay_vcdp_provenance_replay
    (certificateDigest originalFormulaFingerprint solverBuildEvidence
      checkerReplayTranscript reconstructionMapping fallbackNoClaim :
      Prop) :
    ay_vcdp_provenance certificateDigest originalFormulaFingerprint
      solverBuildEvidence checkerReplayTranscript reconstructionMapping
      fallbackNoClaim ->
    checkerReplayTranscript :=
  fun provenance =>
    ay_vcdp_conj_right certificateDigest
      (ay_vcdp_conj originalFormulaFingerprint
        (ay_vcdp_conj solverBuildEvidence
          (ay_vcdp_conj checkerReplayTranscript
            (ay_vcdp_conj reconstructionMapping fallbackNoClaim))))
      provenance checkerReplayTranscript
      (fun _fingerprintProof tail =>
        tail checkerReplayTranscript
          (fun _buildProof tail2 =>
            tail2 checkerReplayTranscript
              (fun replayProof _tail3 => replayProof)))

theorem ay_vcdp_provenance_reconstruction
    (certificateDigest originalFormulaFingerprint solverBuildEvidence
      checkerReplayTranscript reconstructionMapping fallbackNoClaim :
      Prop) :
    ay_vcdp_provenance certificateDigest originalFormulaFingerprint
      solverBuildEvidence checkerReplayTranscript reconstructionMapping
      fallbackNoClaim ->
    reconstructionMapping :=
  fun provenance =>
    ay_vcdp_conj_right certificateDigest
      (ay_vcdp_conj originalFormulaFingerprint
        (ay_vcdp_conj solverBuildEvidence
          (ay_vcdp_conj checkerReplayTranscript
            (ay_vcdp_conj reconstructionMapping fallbackNoClaim))))
      provenance reconstructionMapping
      (fun _fingerprintProof tail =>
        tail reconstructionMapping
          (fun _buildProof tail2 =>
            tail2 reconstructionMapping
              (fun _replayProof tail3 =>
                tail3 reconstructionMapping
                  (fun reconstructionProof _fallbackProof =>
                    reconstructionProof))))

theorem ay_vcdp_provenance_fallback
    (certificateDigest originalFormulaFingerprint solverBuildEvidence
      checkerReplayTranscript reconstructionMapping fallbackNoClaim :
      Prop) :
    ay_vcdp_provenance certificateDigest originalFormulaFingerprint
      solverBuildEvidence checkerReplayTranscript reconstructionMapping
      fallbackNoClaim ->
    fallbackNoClaim :=
  fun provenance =>
    ay_vcdp_conj_right certificateDigest
      (ay_vcdp_conj originalFormulaFingerprint
        (ay_vcdp_conj solverBuildEvidence
          (ay_vcdp_conj checkerReplayTranscript
            (ay_vcdp_conj reconstructionMapping fallbackNoClaim))))
      provenance fallbackNoClaim
      (fun _fingerprintProof tail =>
        tail fallbackNoClaim
          (fun _buildProof tail2 =>
            tail2 fallbackNoClaim
              (fun _replayProof tail3 =>
                tail3 fallbackNoClaim
                  (fun _reconstructionProof fallbackProof =>
                    fallbackProof))))

theorem ay_vcdp_sat_certificate_intro
    (provenance modelCertificate originalModel : Prop) :
    provenance -> modelCertificate -> originalModel ->
    ay_vcdp_sat_certificate provenance modelCertificate originalModel :=
  fun provenanceProof modelProof originalProof =>
    ay_vcdp_conj_intro provenance
      (ay_vcdp_conj modelCertificate originalModel)
      provenanceProof
      (ay_vcdp_conj_intro modelCertificate originalModel modelProof
        originalProof)

theorem ay_vcdp_sat_certificate_provenance
    (provenance modelCertificate originalModel : Prop) :
    ay_vcdp_sat_certificate provenance modelCertificate originalModel ->
    provenance :=
  fun certificate =>
    ay_vcdp_conj_left provenance
      (ay_vcdp_conj modelCertificate originalModel) certificate

theorem ay_vcdp_sat_certificate_original_model
    (provenance modelCertificate originalModel : Prop) :
    ay_vcdp_sat_certificate provenance modelCertificate originalModel ->
    originalModel :=
  fun certificate =>
    ay_vcdp_conj_right provenance
      (ay_vcdp_conj modelCertificate originalModel)
      certificate originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vcdp_unsat_certificate_intro
    (provenance proofCertificate originalEmptyClause : Prop) :
    provenance -> proofCertificate -> originalEmptyClause ->
    ay_vcdp_unsat_certificate provenance proofCertificate
      originalEmptyClause :=
  fun provenanceProof proofProof emptyProof =>
    ay_vcdp_conj_intro provenance
      (ay_vcdp_conj proofCertificate originalEmptyClause)
      provenanceProof
      (ay_vcdp_conj_intro proofCertificate originalEmptyClause proofProof
        emptyProof)

theorem ay_vcdp_unsat_certificate_provenance
    (provenance proofCertificate originalEmptyClause : Prop) :
    ay_vcdp_unsat_certificate provenance proofCertificate
      originalEmptyClause ->
    provenance :=
  fun certificate =>
    ay_vcdp_conj_left provenance
      (ay_vcdp_conj proofCertificate originalEmptyClause) certificate

theorem ay_vcdp_unsat_certificate_original_empty_clause
    (provenance proofCertificate originalEmptyClause : Prop) :
    ay_vcdp_unsat_certificate provenance proofCertificate
      originalEmptyClause ->
    originalEmptyClause :=
  fun certificate =>
    ay_vcdp_conj_right provenance
      (ay_vcdp_conj proofCertificate originalEmptyClause)
      certificate originalEmptyClause
      (fun _proofProof emptyProof => emptyProof)

theorem ay_vcdp_no_claim_intro
    (provenance diagnostic noSemanticClaim : Prop) :
    provenance -> diagnostic -> noSemanticClaim ->
    ay_vcdp_no_claim provenance diagnostic noSemanticClaim :=
  fun provenanceProof diagnosticProof noClaimProof =>
    ay_vcdp_conj_intro provenance
      (ay_vcdp_conj diagnostic noSemanticClaim)
      provenanceProof
      (ay_vcdp_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vcdp_no_claim_no_semantic_claim
    (provenance diagnostic noSemanticClaim : Prop) :
    ay_vcdp_no_claim provenance diagnostic noSemanticClaim ->
    noSemanticClaim :=
  fun claim =>
    ay_vcdp_conj_right provenance
      (ay_vcdp_conj diagnostic noSemanticClaim)
      claim noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vcdp_accepted_sat_provenance_preserves_soundness
    (provenance modelCertificate originalModel unsatFact noClaimFact :
      Prop) :
    ay_vcdp_sat_certificate provenance modelCertificate originalModel ->
    ay_vcdp_public_result originalModel unsatFact noClaimFact :=
  fun certificate =>
    ay_vcdp_disj_left originalModel
      (ay_vcdp_disj unsatFact noClaimFact)
      (ay_vcdp_sat_certificate_original_model provenance modelCertificate
        originalModel certificate)

theorem ay_vcdp_accepted_unsat_provenance_preserves_soundness
    (satFact provenance proofCertificate originalEmptyClause noClaimFact :
      Prop) :
    ay_vcdp_unsat_certificate provenance proofCertificate
      originalEmptyClause ->
    ay_vcdp_public_result satFact originalEmptyClause noClaimFact :=
  fun certificate =>
    ay_vcdp_disj_right satFact
      (ay_vcdp_disj originalEmptyClause noClaimFact)
      (ay_vcdp_disj_left originalEmptyClause noClaimFact
        (ay_vcdp_unsat_certificate_original_empty_clause provenance
          proofCertificate originalEmptyClause certificate))

theorem ay_vcdp_no_claim_preserves_public_no_claim
    (satFact unsatFact provenance diagnostic noSemanticClaim : Prop) :
    ay_vcdp_no_claim provenance diagnostic noSemanticClaim ->
    ay_vcdp_public_result satFact unsatFact noSemanticClaim :=
  fun claim =>
    ay_vcdp_disj_right satFact
      (ay_vcdp_disj unsatFact noSemanticClaim)
      (ay_vcdp_disj_right unsatFact noSemanticClaim
        (ay_vcdp_no_claim_no_semantic_claim provenance diagnostic
          noSemanticClaim claim))

theorem ay_vcdp_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vcdp_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vcdp_conj_intro reason
      (ay_vcdp_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vcdp_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vcdp_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vcdp_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vcdp_conj_right reason
      (ay_vcdp_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vcdp_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vcdp_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vcdp_conj_right reason
      (ay_vcdp_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vcdp_recompute_intro
    (reason fallbackNoClaim fallbackPath : Prop) :
    reason -> fallbackNoClaim -> fallbackPath ->
    ay_vcdp_recompute reason fallbackNoClaim fallbackPath :=
  fun reasonProof fallbackProof pathProof =>
    ay_vcdp_conj_intro reason
      (ay_vcdp_conj fallbackNoClaim fallbackPath)
      reasonProof
      (ay_vcdp_conj_intro fallbackNoClaim fallbackPath fallbackProof
        pathProof)

theorem ay_vcdp_provenance_failure_intro
    (satFact unsatFact reason fallbackNoClaim fallbackPath : Prop) :
    ay_vcdp_blocked_publication satFact unsatFact reason ->
    ay_vcdp_recompute reason fallbackNoClaim fallbackPath ->
    ay_vcdp_provenance_failure satFact unsatFact reason fallbackNoClaim
      fallbackPath :=
  fun blocked recompute =>
    ay_vcdp_conj_intro
      (ay_vcdp_blocked_publication satFact unsatFact reason)
      (ay_vcdp_recompute reason fallbackNoClaim fallbackPath)
      blocked recompute

theorem ay_vcdp_provenance_failure_blocks_sat
    (satFact unsatFact reason fallbackNoClaim fallbackPath : Prop) :
    ay_vcdp_provenance_failure satFact unsatFact reason fallbackNoClaim
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vcdp_blocked_publication_no_sat satFact unsatFact reason
      (ay_vcdp_conj_left
        (ay_vcdp_blocked_publication satFact unsatFact reason)
        (ay_vcdp_recompute reason fallbackNoClaim fallbackPath)
        failure)

theorem ay_vcdp_provenance_failure_blocks_unsat
    (satFact unsatFact reason fallbackNoClaim fallbackPath : Prop) :
    ay_vcdp_provenance_failure satFact unsatFact reason fallbackNoClaim
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vcdp_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vcdp_conj_left
        (ay_vcdp_blocked_publication satFact unsatFact reason)
        (ay_vcdp_recompute reason fallbackNoClaim fallbackPath)
        failure)

theorem ay_vcdp_provenance_failure_recompute
    (satFact unsatFact reason fallbackNoClaim fallbackPath : Prop) :
    ay_vcdp_provenance_failure satFact unsatFact reason fallbackNoClaim
      fallbackPath ->
    ay_vcdp_recompute reason fallbackNoClaim fallbackPath :=
  fun failure =>
    ay_vcdp_conj_right
      (ay_vcdp_blocked_publication satFact unsatFact reason)
      (ay_vcdp_recompute reason fallbackNoClaim fallbackPath)
      failure

theorem ay_vcdp_digest_drift_forces_no_claim
    (satFact unsatFact digestDrift fallbackNoClaim fallbackPath : Prop) :
    digestDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackNoClaim -> fallbackPath ->
    ay_vcdp_provenance_failure satFact unsatFact digestDrift
      fallbackNoClaim fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vcdp_provenance_failure_intro satFact unsatFact digestDrift
      fallbackNoClaim fallbackPath
      (ay_vcdp_blocked_publication_intro satFact unsatFact digestDrift
        reasonProof blockSat blockUnsat)
      (ay_vcdp_recompute_intro digestDrift fallbackNoClaim fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vcdp_provenance_drift_forces_no_claim
    (satFact unsatFact provenanceDrift fallbackNoClaim fallbackPath : Prop) :
    provenanceDrift -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackNoClaim -> fallbackPath ->
    ay_vcdp_provenance_failure satFact unsatFact provenanceDrift
      fallbackNoClaim fallbackPath :=
  fun reasonProof blockSat blockUnsat fallbackProof pathProof =>
    ay_vcdp_provenance_failure_intro satFact unsatFact provenanceDrift
      fallbackNoClaim fallbackPath
      (ay_vcdp_blocked_publication_intro satFact unsatFact provenanceDrift
        reasonProof blockSat blockUnsat)
      (ay_vcdp_recompute_intro provenanceDrift fallbackNoClaim fallbackPath
        reasonProof fallbackProof pathProof)

theorem ay_vcdp_stale_certificate_cannot_bless_sat
    (satFact unsatFact staleCertificate fallbackNoClaim fallbackPath : Prop) :
    ay_vcdp_provenance_failure satFact unsatFact staleCertificate
      fallbackNoClaim fallbackPath ->
    satFact -> False :=
  ay_vcdp_provenance_failure_blocks_sat satFact unsatFact staleCertificate
    fallbackNoClaim fallbackPath

theorem ay_vcdp_stale_certificate_cannot_bless_unsat
    (satFact unsatFact staleCertificate fallbackNoClaim fallbackPath : Prop) :
    ay_vcdp_provenance_failure satFact unsatFact staleCertificate
      fallbackNoClaim fallbackPath ->
    unsatFact -> False :=
  ay_vcdp_provenance_failure_blocks_unsat satFact unsatFact staleCertificate
    fallbackNoClaim fallbackPath

theorem ay_vcdp_mismatched_certificate_cannot_bless_sat
    (satFact unsatFact mismatch fallbackNoClaim fallbackPath : Prop) :
    ay_vcdp_provenance_failure satFact unsatFact mismatch fallbackNoClaim
      fallbackPath ->
    satFact -> False :=
  ay_vcdp_provenance_failure_blocks_sat satFact unsatFact mismatch
    fallbackNoClaim fallbackPath

theorem ay_vcdp_mismatched_certificate_cannot_bless_unsat
    (satFact unsatFact mismatch fallbackNoClaim fallbackPath : Prop) :
    ay_vcdp_provenance_failure satFact unsatFact mismatch fallbackNoClaim
      fallbackPath ->
    unsatFact -> False :=
  ay_vcdp_provenance_failure_blocks_unsat satFact unsatFact mismatch
    fallbackNoClaim fallbackPath
