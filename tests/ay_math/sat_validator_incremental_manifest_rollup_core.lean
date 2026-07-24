-- SAT-COMP validator incremental manifest rollup core.
--
-- Per-phase manifests may be rolled up into one public manifest only when
-- every phase retains the original input fingerprint, solver build identity,
-- artifact digest, replay transcript, reconstruction handle, exit-code
-- mapping, and audit fallback evidence.

def ay_vimr_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vimr_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vimr_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vimr_disj satFact (ay_vimr_disj unsatFact noClaimFact)

def ay_vimr_phase_manifest
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) : Prop :=
  ay_vimr_conj originalFingerprint
    (ay_vimr_conj solverBuildIdentity
      (ay_vimr_conj artifactDigest
        (ay_vimr_conj checkerReplayTranscript
          (ay_vimr_conj reconstructionHandle
            (ay_vimr_conj exitCodeMapping auditFallback)))))

def ay_vimr_rollup_contract
    (allPhaseManifests rollupDigestAgreement rollupAuditTrail : Prop) :
    Prop :=
  ay_vimr_conj allPhaseManifests
    (ay_vimr_conj rollupDigestAgreement rollupAuditTrail)

def ay_vimr_sat_rollup
    (rollupContract modelEvidence originalModel : Prop) : Prop :=
  ay_vimr_conj rollupContract
    (ay_vimr_conj modelEvidence originalModel)

def ay_vimr_unsat_rollup
    (rollupContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vimr_conj rollupContract
    (ay_vimr_conj proofEvidence originalEmptyClause)

def ay_vimr_no_claim_rollup
    (rollupContract diagnostic noSemanticClaim : Prop) : Prop :=
  ay_vimr_conj rollupContract
    (ay_vimr_conj diagnostic noSemanticClaim)

def ay_vimr_component_result
    (componentManifest componentEvidence publicEvidence : Prop) : Prop :=
  ay_vimr_conj componentManifest
    (ay_vimr_conj componentEvidence publicEvidence)

def ay_vimr_rollup_validation
    (rollupContract componentResults publicEvidence : Prop) : Prop :=
  ay_vimr_conj rollupContract
    (ay_vimr_conj componentResults publicEvidence)

def ay_vimr_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vimr_conj reason
    (ay_vimr_conj (satFact -> False) (unsatFact -> False))

def ay_vimr_recompute
    (reason auditFallback fallbackPath : Prop) : Prop :=
  ay_vimr_conj reason (ay_vimr_conj auditFallback fallbackPath)

def ay_vimr_rollup_failure
    (satFact unsatFact reason auditFallback fallbackPath : Prop) : Prop :=
  ay_vimr_conj
    (ay_vimr_blocked_publication satFact unsatFact reason)
    (ay_vimr_recompute reason auditFallback fallbackPath)

theorem ay_vimr_conj_intro (left right : Prop) :
    left -> right -> ay_vimr_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vimr_conj_left (left right : Prop) :
    ay_vimr_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vimr_conj_right (left right : Prop) :
    ay_vimr_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vimr_disj_left (left right : Prop) :
    left -> ay_vimr_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vimr_disj_right (left right : Prop) :
    right -> ay_vimr_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vimr_phase_manifest_intro
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    originalFingerprint -> solverBuildIdentity -> artifactDigest ->
    checkerReplayTranscript -> reconstructionHandle -> exitCodeMapping ->
    auditFallback ->
    ay_vimr_phase_manifest originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback :=
  fun fingerprintProof buildProof digestProof replayProof reconstructionProof
      mappingProof auditProof =>
    ay_vimr_conj_intro originalFingerprint
      (ay_vimr_conj solverBuildIdentity
        (ay_vimr_conj artifactDigest
          (ay_vimr_conj checkerReplayTranscript
            (ay_vimr_conj reconstructionHandle
              (ay_vimr_conj exitCodeMapping auditFallback)))))
      fingerprintProof
      (ay_vimr_conj_intro solverBuildIdentity
        (ay_vimr_conj artifactDigest
          (ay_vimr_conj checkerReplayTranscript
            (ay_vimr_conj reconstructionHandle
              (ay_vimr_conj exitCodeMapping auditFallback))))
        buildProof
        (ay_vimr_conj_intro artifactDigest
          (ay_vimr_conj checkerReplayTranscript
            (ay_vimr_conj reconstructionHandle
              (ay_vimr_conj exitCodeMapping auditFallback)))
          digestProof
          (ay_vimr_conj_intro checkerReplayTranscript
            (ay_vimr_conj reconstructionHandle
              (ay_vimr_conj exitCodeMapping auditFallback))
            replayProof
            (ay_vimr_conj_intro reconstructionHandle
              (ay_vimr_conj exitCodeMapping auditFallback)
              reconstructionProof
              (ay_vimr_conj_intro exitCodeMapping auditFallback
                mappingProof auditProof)))))

theorem ay_vimr_phase_manifest_fingerprint
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vimr_phase_manifest originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    originalFingerprint :=
  fun manifest =>
    ay_vimr_conj_left originalFingerprint
      (ay_vimr_conj solverBuildIdentity
        (ay_vimr_conj artifactDigest
          (ay_vimr_conj checkerReplayTranscript
            (ay_vimr_conj reconstructionHandle
              (ay_vimr_conj exitCodeMapping auditFallback)))))
      manifest

theorem ay_vimr_phase_manifest_build
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vimr_phase_manifest originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    solverBuildIdentity :=
  fun manifest =>
    ay_vimr_conj_right originalFingerprint
      (ay_vimr_conj solverBuildIdentity
        (ay_vimr_conj artifactDigest
          (ay_vimr_conj checkerReplayTranscript
            (ay_vimr_conj reconstructionHandle
              (ay_vimr_conj exitCodeMapping auditFallback)))))
      manifest solverBuildIdentity
      (fun buildProof _tail => buildProof)

theorem ay_vimr_phase_manifest_digest
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vimr_phase_manifest originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    artifactDigest :=
  fun manifest =>
    ay_vimr_conj_right originalFingerprint
      (ay_vimr_conj solverBuildIdentity
        (ay_vimr_conj artifactDigest
          (ay_vimr_conj checkerReplayTranscript
            (ay_vimr_conj reconstructionHandle
              (ay_vimr_conj exitCodeMapping auditFallback)))))
      manifest artifactDigest
      (fun _buildProof tail =>
        tail artifactDigest (fun digestProof _tail2 => digestProof))

theorem ay_vimr_phase_manifest_replay
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vimr_phase_manifest originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    checkerReplayTranscript :=
  fun manifest =>
    ay_vimr_conj_right originalFingerprint
      (ay_vimr_conj solverBuildIdentity
        (ay_vimr_conj artifactDigest
          (ay_vimr_conj checkerReplayTranscript
            (ay_vimr_conj reconstructionHandle
              (ay_vimr_conj exitCodeMapping auditFallback)))))
      manifest checkerReplayTranscript
      (fun _buildProof tail =>
        tail checkerReplayTranscript
          (fun _digestProof tail2 =>
            tail2 checkerReplayTranscript
              (fun replayProof _tail3 => replayProof)))

theorem ay_vimr_phase_manifest_reconstruction
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vimr_phase_manifest originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    reconstructionHandle :=
  fun manifest =>
    ay_vimr_conj_right originalFingerprint
      (ay_vimr_conj solverBuildIdentity
        (ay_vimr_conj artifactDigest
          (ay_vimr_conj checkerReplayTranscript
            (ay_vimr_conj reconstructionHandle
              (ay_vimr_conj exitCodeMapping auditFallback)))))
      manifest reconstructionHandle
      (fun _buildProof tail =>
        tail reconstructionHandle
          (fun _digestProof tail2 =>
            tail2 reconstructionHandle
              (fun _replayProof tail3 =>
                tail3 reconstructionHandle
                  (fun reconstructionProof _tail4 =>
                    reconstructionProof))))

theorem ay_vimr_phase_manifest_mapping
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vimr_phase_manifest originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    exitCodeMapping :=
  fun manifest =>
    ay_vimr_conj_right originalFingerprint
      (ay_vimr_conj solverBuildIdentity
        (ay_vimr_conj artifactDigest
          (ay_vimr_conj checkerReplayTranscript
            (ay_vimr_conj reconstructionHandle
              (ay_vimr_conj exitCodeMapping auditFallback)))))
      manifest exitCodeMapping
      (fun _buildProof tail =>
        tail exitCodeMapping
          (fun _digestProof tail2 =>
            tail2 exitCodeMapping
              (fun _replayProof tail3 =>
                tail3 exitCodeMapping
                  (fun _reconstructionProof tail4 =>
                    tail4 exitCodeMapping
                      (fun mappingProof _auditProof => mappingProof)))))

theorem ay_vimr_phase_manifest_audit
    (originalFingerprint solverBuildIdentity artifactDigest
      checkerReplayTranscript reconstructionHandle exitCodeMapping
      auditFallback : Prop) :
    ay_vimr_phase_manifest originalFingerprint solverBuildIdentity
      artifactDigest checkerReplayTranscript reconstructionHandle
      exitCodeMapping auditFallback ->
    auditFallback :=
  fun manifest =>
    ay_vimr_conj_right originalFingerprint
      (ay_vimr_conj solverBuildIdentity
        (ay_vimr_conj artifactDigest
          (ay_vimr_conj checkerReplayTranscript
            (ay_vimr_conj reconstructionHandle
              (ay_vimr_conj exitCodeMapping auditFallback)))))
      manifest auditFallback
      (fun _buildProof tail =>
        tail auditFallback
          (fun _digestProof tail2 =>
            tail2 auditFallback
              (fun _replayProof tail3 =>
                tail3 auditFallback
                  (fun _reconstructionProof tail4 =>
                    tail4 auditFallback
                      (fun _mappingProof auditProof => auditProof)))))

theorem ay_vimr_rollup_contract_intro
    (allPhaseManifests rollupDigestAgreement rollupAuditTrail : Prop) :
    allPhaseManifests -> rollupDigestAgreement -> rollupAuditTrail ->
    ay_vimr_rollup_contract allPhaseManifests rollupDigestAgreement
      rollupAuditTrail :=
  fun phasesProof digestProof auditProof =>
    ay_vimr_conj_intro allPhaseManifests
      (ay_vimr_conj rollupDigestAgreement rollupAuditTrail)
      phasesProof
      (ay_vimr_conj_intro rollupDigestAgreement rollupAuditTrail
        digestProof auditProof)

theorem ay_vimr_rollup_contract_phases
    (allPhaseManifests rollupDigestAgreement rollupAuditTrail : Prop) :
    ay_vimr_rollup_contract allPhaseManifests rollupDigestAgreement
      rollupAuditTrail ->
    allPhaseManifests :=
  fun contract =>
    ay_vimr_conj_left allPhaseManifests
      (ay_vimr_conj rollupDigestAgreement rollupAuditTrail) contract

theorem ay_vimr_rollup_contract_digest
    (allPhaseManifests rollupDigestAgreement rollupAuditTrail : Prop) :
    ay_vimr_rollup_contract allPhaseManifests rollupDigestAgreement
      rollupAuditTrail ->
    rollupDigestAgreement :=
  fun contract =>
    ay_vimr_conj_right allPhaseManifests
      (ay_vimr_conj rollupDigestAgreement rollupAuditTrail)
      contract rollupDigestAgreement
      (fun digestProof _auditProof => digestProof)

theorem ay_vimr_rollup_contract_audit
    (allPhaseManifests rollupDigestAgreement rollupAuditTrail : Prop) :
    ay_vimr_rollup_contract allPhaseManifests rollupDigestAgreement
      rollupAuditTrail ->
    rollupAuditTrail :=
  fun contract =>
    ay_vimr_conj_right allPhaseManifests
      (ay_vimr_conj rollupDigestAgreement rollupAuditTrail)
      contract rollupAuditTrail
      (fun _digestProof auditProof => auditProof)

theorem ay_vimr_sat_rollup_intro
    (rollupContract modelEvidence originalModel : Prop) :
    rollupContract -> modelEvidence -> originalModel ->
    ay_vimr_sat_rollup rollupContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vimr_conj_intro rollupContract
      (ay_vimr_conj modelEvidence originalModel)
      contractProof
      (ay_vimr_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vimr_sat_rollup_contract
    (rollupContract modelEvidence originalModel : Prop) :
    ay_vimr_sat_rollup rollupContract modelEvidence originalModel ->
    rollupContract :=
  fun rollup =>
    ay_vimr_conj_left rollupContract
      (ay_vimr_conj modelEvidence originalModel) rollup

theorem ay_vimr_sat_rollup_original_model
    (rollupContract modelEvidence originalModel : Prop) :
    ay_vimr_sat_rollup rollupContract modelEvidence originalModel ->
    originalModel :=
  fun rollup =>
    ay_vimr_conj_right rollupContract
      (ay_vimr_conj modelEvidence originalModel)
      rollup originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vimr_unsat_rollup_intro
    (rollupContract proofEvidence originalEmptyClause : Prop) :
    rollupContract -> proofEvidence -> originalEmptyClause ->
    ay_vimr_unsat_rollup rollupContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof emptyProof =>
    ay_vimr_conj_intro rollupContract
      (ay_vimr_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vimr_conj_intro proofEvidence originalEmptyClause proofProof
        emptyProof)

theorem ay_vimr_unsat_rollup_contract
    (rollupContract proofEvidence originalEmptyClause : Prop) :
    ay_vimr_unsat_rollup rollupContract proofEvidence
      originalEmptyClause ->
    rollupContract :=
  fun rollup =>
    ay_vimr_conj_left rollupContract
      (ay_vimr_conj proofEvidence originalEmptyClause) rollup

theorem ay_vimr_unsat_rollup_original_empty_clause
    (rollupContract proofEvidence originalEmptyClause : Prop) :
    ay_vimr_unsat_rollup rollupContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun rollup =>
    ay_vimr_conj_right rollupContract
      (ay_vimr_conj proofEvidence originalEmptyClause)
      rollup originalEmptyClause
      (fun _proofProof emptyProof => emptyProof)

theorem ay_vimr_no_claim_rollup_intro
    (rollupContract diagnostic noSemanticClaim : Prop) :
    rollupContract -> diagnostic -> noSemanticClaim ->
    ay_vimr_no_claim_rollup rollupContract diagnostic noSemanticClaim :=
  fun contractProof diagnosticProof noClaimProof =>
    ay_vimr_conj_intro rollupContract
      (ay_vimr_conj diagnostic noSemanticClaim)
      contractProof
      (ay_vimr_conj_intro diagnostic noSemanticClaim diagnosticProof
        noClaimProof)

theorem ay_vimr_no_claim_rollup_no_semantic_claim
    (rollupContract diagnostic noSemanticClaim : Prop) :
    ay_vimr_no_claim_rollup rollupContract diagnostic noSemanticClaim ->
    noSemanticClaim :=
  fun rollup =>
    ay_vimr_conj_right rollupContract
      (ay_vimr_conj diagnostic noSemanticClaim)
      rollup noSemanticClaim
      (fun _diagnosticProof noClaimProof => noClaimProof)

theorem ay_vimr_component_result_intro
    (componentManifest componentEvidence publicEvidence : Prop) :
    componentManifest -> componentEvidence -> publicEvidence ->
    ay_vimr_component_result componentManifest componentEvidence
      publicEvidence :=
  fun manifestProof evidenceProof publicProof =>
    ay_vimr_conj_intro componentManifest
      (ay_vimr_conj componentEvidence publicEvidence)
      manifestProof
      (ay_vimr_conj_intro componentEvidence publicEvidence evidenceProof
        publicProof)

theorem ay_vimr_component_result_public
    (componentManifest componentEvidence publicEvidence : Prop) :
    ay_vimr_component_result componentManifest componentEvidence
      publicEvidence ->
    publicEvidence :=
  fun component =>
    ay_vimr_conj_right componentManifest
      (ay_vimr_conj componentEvidence publicEvidence)
      component publicEvidence
      (fun _evidenceProof publicProof => publicProof)

theorem ay_vimr_rollup_validation_intro
    (rollupContract componentResults publicEvidence : Prop) :
    rollupContract -> componentResults -> publicEvidence ->
    ay_vimr_rollup_validation rollupContract componentResults
      publicEvidence :=
  fun contractProof componentsProof publicProof =>
    ay_vimr_conj_intro rollupContract
      (ay_vimr_conj componentResults publicEvidence)
      contractProof
      (ay_vimr_conj_intro componentResults publicEvidence componentsProof
        publicProof)

theorem ay_vimr_rollup_validation_public
    (rollupContract componentResults publicEvidence : Prop) :
    ay_vimr_rollup_validation rollupContract componentResults
      publicEvidence ->
    publicEvidence :=
  fun validation =>
    ay_vimr_conj_right rollupContract
      (ay_vimr_conj componentResults publicEvidence)
      validation publicEvidence
      (fun _componentsProof publicProof => publicProof)

theorem ay_vimr_sat_rollup_validates_same_result
    (rollupContract modelEvidence originalModel unsatFact noClaimFact :
      Prop) :
    ay_vimr_sat_rollup rollupContract modelEvidence originalModel ->
    ay_vimr_public_result originalModel unsatFact noClaimFact :=
  fun rollup =>
    ay_vimr_disj_left originalModel
      (ay_vimr_disj unsatFact noClaimFact)
      (ay_vimr_sat_rollup_original_model rollupContract modelEvidence
        originalModel rollup)

theorem ay_vimr_unsat_rollup_validates_same_result
    (satFact rollupContract proofEvidence originalEmptyClause noClaimFact :
      Prop) :
    ay_vimr_unsat_rollup rollupContract proofEvidence
      originalEmptyClause ->
    ay_vimr_public_result satFact originalEmptyClause noClaimFact :=
  fun rollup =>
    ay_vimr_disj_right satFact
      (ay_vimr_disj originalEmptyClause noClaimFact)
      (ay_vimr_disj_left originalEmptyClause noClaimFact
        (ay_vimr_unsat_rollup_original_empty_clause rollupContract
          proofEvidence originalEmptyClause rollup))

theorem ay_vimr_no_claim_rollup_validates_same_result
    (satFact unsatFact rollupContract diagnostic noSemanticClaim : Prop) :
    ay_vimr_no_claim_rollup rollupContract diagnostic noSemanticClaim ->
    ay_vimr_public_result satFact unsatFact noSemanticClaim :=
  fun rollup =>
    ay_vimr_disj_right satFact
      (ay_vimr_disj unsatFact noSemanticClaim)
      (ay_vimr_disj_right unsatFact noSemanticClaim
        (ay_vimr_no_claim_rollup_no_semantic_claim rollupContract
          diagnostic noSemanticClaim rollup))

theorem ay_vimr_sat_rollup_matches_components
    (rollupContract modelEvidence originalModel componentResults : Prop) :
    ay_vimr_sat_rollup rollupContract modelEvidence originalModel ->
    componentResults ->
    ay_vimr_rollup_validation rollupContract componentResults originalModel :=
  fun rollup componentsProof =>
    ay_vimr_rollup_validation_intro rollupContract componentResults
      originalModel
      (ay_vimr_sat_rollup_contract rollupContract modelEvidence
        originalModel rollup)
      componentsProof
      (ay_vimr_sat_rollup_original_model rollupContract modelEvidence
        originalModel rollup)

theorem ay_vimr_unsat_rollup_matches_components
    (rollupContract proofEvidence originalEmptyClause componentResults :
      Prop) :
    ay_vimr_unsat_rollup rollupContract proofEvidence originalEmptyClause ->
    componentResults ->
    ay_vimr_rollup_validation rollupContract componentResults
      originalEmptyClause :=
  fun rollup componentsProof =>
    ay_vimr_rollup_validation_intro rollupContract componentResults
      originalEmptyClause
      (ay_vimr_unsat_rollup_contract rollupContract proofEvidence
        originalEmptyClause rollup)
      componentsProof
      (ay_vimr_unsat_rollup_original_empty_clause rollupContract
        proofEvidence originalEmptyClause rollup)

theorem ay_vimr_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vimr_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vimr_conj_intro reason
      (ay_vimr_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vimr_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vimr_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vimr_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vimr_conj_right reason
      (ay_vimr_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vimr_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vimr_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vimr_conj_right reason
      (ay_vimr_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vimr_recompute_intro
    (reason auditFallback fallbackPath : Prop) :
    reason -> auditFallback -> fallbackPath ->
    ay_vimr_recompute reason auditFallback fallbackPath :=
  fun reasonProof auditProof pathProof =>
    ay_vimr_conj_intro reason
      (ay_vimr_conj auditFallback fallbackPath)
      reasonProof
      (ay_vimr_conj_intro auditFallback fallbackPath auditProof pathProof)

theorem ay_vimr_rollup_failure_intro
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vimr_blocked_publication satFact unsatFact reason ->
    ay_vimr_recompute reason auditFallback fallbackPath ->
    ay_vimr_rollup_failure satFact unsatFact reason auditFallback
      fallbackPath :=
  fun blocked recompute =>
    ay_vimr_conj_intro
      (ay_vimr_blocked_publication satFact unsatFact reason)
      (ay_vimr_recompute reason auditFallback fallbackPath)
      blocked recompute

theorem ay_vimr_rollup_failure_blocks_sat
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vimr_rollup_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vimr_blocked_publication_no_sat satFact unsatFact reason
      (ay_vimr_conj_left
        (ay_vimr_blocked_publication satFact unsatFact reason)
        (ay_vimr_recompute reason auditFallback fallbackPath)
        failure)

theorem ay_vimr_rollup_failure_blocks_unsat
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vimr_rollup_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vimr_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vimr_conj_left
        (ay_vimr_blocked_publication satFact unsatFact reason)
        (ay_vimr_recompute reason auditFallback fallbackPath)
        failure)

theorem ay_vimr_rollup_failure_recompute
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vimr_rollup_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    ay_vimr_recompute reason auditFallback fallbackPath :=
  fun failure =>
    ay_vimr_conj_right
      (ay_vimr_blocked_publication satFact unsatFact reason)
      (ay_vimr_recompute reason auditFallback fallbackPath)
      failure

theorem ay_vimr_missing_phase_forces_no_claim
    (satFact unsatFact missingPhase auditFallback fallbackPath : Prop) :
    missingPhase -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vimr_rollup_failure satFact unsatFact missingPhase auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vimr_rollup_failure_intro satFact unsatFact missingPhase
      auditFallback fallbackPath
      (ay_vimr_blocked_publication_intro satFact unsatFact missingPhase
        reasonProof blockSat blockUnsat)
      (ay_vimr_recompute_intro missingPhase auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vimr_digest_disagreement_forces_no_claim
    (satFact unsatFact digestDisagreement auditFallback fallbackPath :
      Prop) :
    digestDisagreement -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vimr_rollup_failure satFact unsatFact digestDisagreement
      auditFallback fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vimr_rollup_failure_intro satFact unsatFact digestDisagreement
      auditFallback fallbackPath
      (ay_vimr_blocked_publication_intro satFact unsatFact
        digestDisagreement reasonProof blockSat blockUnsat)
      (ay_vimr_recompute_intro digestDisagreement auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vimr_stale_build_identity_forces_no_claim
    (satFact unsatFact staleBuild auditFallback fallbackPath : Prop) :
    staleBuild -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vimr_rollup_failure satFact unsatFact staleBuild auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vimr_rollup_failure_intro satFact unsatFact staleBuild auditFallback
      fallbackPath
      (ay_vimr_blocked_publication_intro satFact unsatFact staleBuild
        reasonProof blockSat blockUnsat)
      (ay_vimr_recompute_intro staleBuild auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vimr_replay_gap_forces_no_claim
    (satFact unsatFact replayGap auditFallback fallbackPath : Prop) :
    replayGap -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vimr_rollup_failure satFact unsatFact replayGap auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vimr_rollup_failure_intro satFact unsatFact replayGap auditFallback
      fallbackPath
      (ay_vimr_blocked_publication_intro satFact unsatFact replayGap
        reasonProof blockSat blockUnsat)
      (ay_vimr_recompute_intro replayGap auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vimr_reconstruction_gap_forces_no_claim
    (satFact unsatFact reconstructionGap auditFallback fallbackPath : Prop) :
    reconstructionGap -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vimr_rollup_failure satFact unsatFact reconstructionGap
      auditFallback fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vimr_rollup_failure_intro satFact unsatFact reconstructionGap
      auditFallback fallbackPath
      (ay_vimr_blocked_publication_intro satFact unsatFact
        reconstructionGap reasonProof blockSat blockUnsat)
      (ay_vimr_recompute_intro reconstructionGap auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vimr_exit_code_mismatch_forces_no_claim
    (satFact unsatFact exitMismatch auditFallback fallbackPath : Prop) :
    exitMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vimr_rollup_failure satFact unsatFact exitMismatch auditFallback
      fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vimr_rollup_failure_intro satFact unsatFact exitMismatch
      auditFallback fallbackPath
      (ay_vimr_blocked_publication_intro satFact unsatFact exitMismatch
        reasonProof blockSat blockUnsat)
      (ay_vimr_recompute_intro exitMismatch auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vimr_audit_contradiction_forces_no_claim
    (satFact unsatFact auditContradiction auditFallback fallbackPath : Prop) :
    auditContradiction -> (satFact -> False) -> (unsatFact -> False) ->
    auditFallback -> fallbackPath ->
    ay_vimr_rollup_failure satFact unsatFact auditContradiction
      auditFallback fallbackPath :=
  fun reasonProof blockSat blockUnsat auditProof pathProof =>
    ay_vimr_rollup_failure_intro satFact unsatFact auditContradiction
      auditFallback fallbackPath
      (ay_vimr_blocked_publication_intro satFact unsatFact
        auditContradiction reasonProof blockSat blockUnsat)
      (ay_vimr_recompute_intro auditContradiction auditFallback fallbackPath
        reasonProof auditProof pathProof)

theorem ay_vimr_failure_cannot_publish_sat
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vimr_rollup_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    satFact -> False :=
  ay_vimr_rollup_failure_blocks_sat satFact unsatFact reason auditFallback
    fallbackPath

theorem ay_vimr_failure_cannot_publish_unsat
    (satFact unsatFact reason auditFallback fallbackPath : Prop) :
    ay_vimr_rollup_failure satFact unsatFact reason auditFallback
      fallbackPath ->
    unsatFact -> False :=
  ay_vimr_rollup_failure_blocks_unsat satFact unsatFact reason auditFallback
    fallbackPath
