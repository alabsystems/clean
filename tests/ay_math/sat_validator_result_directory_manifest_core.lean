-- SAT-COMP validator result directory manifest core.
--
-- Result directories may publish SAT/UNSAT only when directory manifest,
-- artifact paths, certificate digests, checker transcript, solver build/config
-- evidence, original formula fingerprint, reconstruction map, and fallback
-- branch are accepted.

def ay_vrdm_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vrdm_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vrdm_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vrdm_disj satFact (ay_vrdm_disj unsatFact noClaimFact)

def ay_vrdm_directory_contract
    (directoryManifest artifactPaths certificateDigests checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) : Prop :=
  ay_vrdm_conj directoryManifest
    (ay_vrdm_conj artifactPaths
      (ay_vrdm_conj certificateDigests
        (ay_vrdm_conj checkerTranscript
          (ay_vrdm_conj solverBuildConfig
            (ay_vrdm_conj originalFormulaFingerprint
              (ay_vrdm_conj reconstructionMap fallbackBranch))))))

def ay_vrdm_sat_publication
    (directoryContract modelCertificate originalModel : Prop) : Prop :=
  ay_vrdm_conj directoryContract
    (ay_vrdm_conj modelCertificate originalModel)

def ay_vrdm_unsat_publication
    (directoryContract proofCertificate originalEmptyClause : Prop) : Prop :=
  ay_vrdm_conj directoryContract
    (ay_vrdm_conj proofCertificate originalEmptyClause)

def ay_vrdm_no_claim
    (reason fallbackBranch auditTrail : Prop) : Prop :=
  ay_vrdm_conj reason (ay_vrdm_conj fallbackBranch auditTrail)

def ay_vrdm_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vrdm_conj reason
    (ay_vrdm_conj (satFact -> False) (unsatFact -> False))

def ay_vrdm_recompute
    (reason fallbackBranch recomputeObligation : Prop) : Prop :=
  ay_vrdm_conj reason
    (ay_vrdm_conj fallbackBranch recomputeObligation)

def ay_vrdm_manifest_failure
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    Prop :=
  ay_vrdm_conj
    (ay_vrdm_blocked_publication satFact unsatFact reason)
    (ay_vrdm_recompute reason fallbackBranch recomputeObligation)

theorem ay_vrdm_conj_intro (left right : Prop) :
    left -> right -> ay_vrdm_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vrdm_conj_left (left right : Prop) :
    ay_vrdm_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vrdm_conj_right (left right : Prop) :
    ay_vrdm_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vrdm_disj_left (left right : Prop) :
    left -> ay_vrdm_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vrdm_disj_right (left right : Prop) :
    right -> ay_vrdm_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vrdm_directory_contract_intro
    (directoryManifest artifactPaths certificateDigests checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    directoryManifest -> artifactPaths -> certificateDigests ->
    checkerTranscript -> solverBuildConfig -> originalFormulaFingerprint ->
    reconstructionMap -> fallbackBranch ->
    ay_vrdm_directory_contract directoryManifest artifactPaths
      certificateDigests checkerTranscript solverBuildConfig
      originalFormulaFingerprint reconstructionMap fallbackBranch :=
  fun manifestProof pathsProof digestsProof transcriptProof buildProof
      fingerprintProof reconstructionProof fallbackProof =>
    ay_vrdm_conj_intro directoryManifest
      (ay_vrdm_conj artifactPaths
        (ay_vrdm_conj certificateDigests
          (ay_vrdm_conj checkerTranscript
            (ay_vrdm_conj solverBuildConfig
              (ay_vrdm_conj originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch))))))
      manifestProof
      (ay_vrdm_conj_intro artifactPaths
        (ay_vrdm_conj certificateDigests
          (ay_vrdm_conj checkerTranscript
            (ay_vrdm_conj solverBuildConfig
              (ay_vrdm_conj originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch)))))
        pathsProof
        (ay_vrdm_conj_intro certificateDigests
          (ay_vrdm_conj checkerTranscript
            (ay_vrdm_conj solverBuildConfig
              (ay_vrdm_conj originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch))))
          digestsProof
          (ay_vrdm_conj_intro checkerTranscript
            (ay_vrdm_conj solverBuildConfig
              (ay_vrdm_conj originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch)))
            transcriptProof
            (ay_vrdm_conj_intro solverBuildConfig
              (ay_vrdm_conj originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch))
              buildProof
              (ay_vrdm_conj_intro originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch)
                fingerprintProof
                (ay_vrdm_conj_intro reconstructionMap fallbackBranch
                  reconstructionProof fallbackProof))))))

theorem ay_vrdm_directory_contract_manifest
    (directoryManifest artifactPaths certificateDigests checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vrdm_directory_contract directoryManifest artifactPaths
      certificateDigests checkerTranscript solverBuildConfig
      originalFormulaFingerprint reconstructionMap fallbackBranch ->
    directoryManifest :=
  fun contract =>
    ay_vrdm_conj_left directoryManifest
      (ay_vrdm_conj artifactPaths
        (ay_vrdm_conj certificateDigests
          (ay_vrdm_conj checkerTranscript
            (ay_vrdm_conj solverBuildConfig
              (ay_vrdm_conj originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch))))))
      contract

theorem ay_vrdm_directory_contract_artifact_paths
    (directoryManifest artifactPaths certificateDigests checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vrdm_directory_contract directoryManifest artifactPaths
      certificateDigests checkerTranscript solverBuildConfig
      originalFormulaFingerprint reconstructionMap fallbackBranch ->
    artifactPaths :=
  fun contract =>
    ay_vrdm_conj_right directoryManifest
      (ay_vrdm_conj artifactPaths
        (ay_vrdm_conj certificateDigests
          (ay_vrdm_conj checkerTranscript
            (ay_vrdm_conj solverBuildConfig
              (ay_vrdm_conj originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch))))))
      contract artifactPaths
      (fun pathsProof _tail => pathsProof)

theorem ay_vrdm_directory_contract_certificate_digests
    (directoryManifest artifactPaths certificateDigests checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vrdm_directory_contract directoryManifest artifactPaths
      certificateDigests checkerTranscript solverBuildConfig
      originalFormulaFingerprint reconstructionMap fallbackBranch ->
    certificateDigests :=
  fun contract =>
    ay_vrdm_conj_right directoryManifest
      (ay_vrdm_conj artifactPaths
        (ay_vrdm_conj certificateDigests
          (ay_vrdm_conj checkerTranscript
            (ay_vrdm_conj solverBuildConfig
              (ay_vrdm_conj originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch))))))
      contract certificateDigests
      (fun _pathsProof tail =>
        tail certificateDigests
          (fun digestsProof _tail2 => digestsProof))

theorem ay_vrdm_directory_contract_checker_transcript
    (directoryManifest artifactPaths certificateDigests checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vrdm_directory_contract directoryManifest artifactPaths
      certificateDigests checkerTranscript solverBuildConfig
      originalFormulaFingerprint reconstructionMap fallbackBranch ->
    checkerTranscript :=
  fun contract =>
    ay_vrdm_conj_right directoryManifest
      (ay_vrdm_conj artifactPaths
        (ay_vrdm_conj certificateDigests
          (ay_vrdm_conj checkerTranscript
            (ay_vrdm_conj solverBuildConfig
              (ay_vrdm_conj originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch))))))
      contract checkerTranscript
      (fun _pathsProof tail =>
        tail checkerTranscript
          (fun _digestsProof tail2 =>
            tail2 checkerTranscript
              (fun transcriptProof _tail3 => transcriptProof)))

theorem ay_vrdm_directory_contract_build_config
    (directoryManifest artifactPaths certificateDigests checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vrdm_directory_contract directoryManifest artifactPaths
      certificateDigests checkerTranscript solverBuildConfig
      originalFormulaFingerprint reconstructionMap fallbackBranch ->
    solverBuildConfig :=
  fun contract =>
    ay_vrdm_conj_right directoryManifest
      (ay_vrdm_conj artifactPaths
        (ay_vrdm_conj certificateDigests
          (ay_vrdm_conj checkerTranscript
            (ay_vrdm_conj solverBuildConfig
              (ay_vrdm_conj originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch))))))
      contract solverBuildConfig
      (fun _pathsProof tail =>
        tail solverBuildConfig
          (fun _digestsProof tail2 =>
            tail2 solverBuildConfig
              (fun _transcriptProof tail3 =>
                tail3 solverBuildConfig
                  (fun buildProof _tail4 => buildProof))))

theorem ay_vrdm_directory_contract_formula_fingerprint
    (directoryManifest artifactPaths certificateDigests checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vrdm_directory_contract directoryManifest artifactPaths
      certificateDigests checkerTranscript solverBuildConfig
      originalFormulaFingerprint reconstructionMap fallbackBranch ->
    originalFormulaFingerprint :=
  fun contract =>
    ay_vrdm_conj_right directoryManifest
      (ay_vrdm_conj artifactPaths
        (ay_vrdm_conj certificateDigests
          (ay_vrdm_conj checkerTranscript
            (ay_vrdm_conj solverBuildConfig
              (ay_vrdm_conj originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch))))))
      contract originalFormulaFingerprint
      (fun _pathsProof tail =>
        tail originalFormulaFingerprint
          (fun _digestsProof tail2 =>
            tail2 originalFormulaFingerprint
              (fun _transcriptProof tail3 =>
                tail3 originalFormulaFingerprint
                  (fun _buildProof tail4 =>
                    tail4 originalFormulaFingerprint
                      (fun fingerprintProof _tail5 => fingerprintProof)))))

theorem ay_vrdm_directory_contract_reconstruction
    (directoryManifest artifactPaths certificateDigests checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vrdm_directory_contract directoryManifest artifactPaths
      certificateDigests checkerTranscript solverBuildConfig
      originalFormulaFingerprint reconstructionMap fallbackBranch ->
    reconstructionMap :=
  fun contract =>
    ay_vrdm_conj_right directoryManifest
      (ay_vrdm_conj artifactPaths
        (ay_vrdm_conj certificateDigests
          (ay_vrdm_conj checkerTranscript
            (ay_vrdm_conj solverBuildConfig
              (ay_vrdm_conj originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch))))))
      contract reconstructionMap
      (fun _pathsProof tail =>
        tail reconstructionMap
          (fun _digestsProof tail2 =>
            tail2 reconstructionMap
              (fun _transcriptProof tail3 =>
                tail3 reconstructionMap
                  (fun _buildProof tail4 =>
                    tail4 reconstructionMap
                      (fun _fingerprintProof tail5 =>
                        tail5 reconstructionMap
                          (fun reconstructionProof _fallbackProof =>
                            reconstructionProof))))))

theorem ay_vrdm_directory_contract_fallback
    (directoryManifest artifactPaths certificateDigests checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch : Prop) :
    ay_vrdm_directory_contract directoryManifest artifactPaths
      certificateDigests checkerTranscript solverBuildConfig
      originalFormulaFingerprint reconstructionMap fallbackBranch ->
    fallbackBranch :=
  fun contract =>
    ay_vrdm_conj_right directoryManifest
      (ay_vrdm_conj artifactPaths
        (ay_vrdm_conj certificateDigests
          (ay_vrdm_conj checkerTranscript
            (ay_vrdm_conj solverBuildConfig
              (ay_vrdm_conj originalFormulaFingerprint
                (ay_vrdm_conj reconstructionMap fallbackBranch))))))
      contract fallbackBranch
      (fun _pathsProof tail =>
        tail fallbackBranch
          (fun _digestsProof tail2 =>
            tail2 fallbackBranch
              (fun _transcriptProof tail3 =>
                tail3 fallbackBranch
                  (fun _buildProof tail4 =>
                    tail4 fallbackBranch
                      (fun _fingerprintProof tail5 =>
                        tail5 fallbackBranch
                          (fun _reconstructionProof fallbackProof =>
                            fallbackProof))))))

theorem ay_vrdm_sat_publication_intro
    (directoryContract modelCertificate originalModel : Prop) :
    directoryContract -> modelCertificate -> originalModel ->
    ay_vrdm_sat_publication directoryContract modelCertificate originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vrdm_conj_intro directoryContract
      (ay_vrdm_conj modelCertificate originalModel)
      contractProof
      (ay_vrdm_conj_intro modelCertificate originalModel
        modelProof originalProof)

theorem ay_vrdm_sat_publication_original_model
    (directoryContract modelCertificate originalModel : Prop) :
    ay_vrdm_sat_publication directoryContract modelCertificate originalModel ->
    originalModel :=
  fun publication =>
    ay_vrdm_conj_right directoryContract
      (ay_vrdm_conj modelCertificate originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vrdm_unsat_publication_intro
    (directoryContract proofCertificate originalEmptyClause : Prop) :
    directoryContract -> proofCertificate -> originalEmptyClause ->
    ay_vrdm_unsat_publication directoryContract proofCertificate
      originalEmptyClause :=
  fun contractProof proofCert originalProof =>
    ay_vrdm_conj_intro directoryContract
      (ay_vrdm_conj proofCertificate originalEmptyClause)
      contractProof
      (ay_vrdm_conj_intro proofCertificate originalEmptyClause
        proofCert originalProof)

theorem ay_vrdm_unsat_publication_original_empty_clause
    (directoryContract proofCertificate originalEmptyClause : Prop) :
    ay_vrdm_unsat_publication directoryContract proofCertificate
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vrdm_conj_right directoryContract
      (ay_vrdm_conj proofCertificate originalEmptyClause)
      publication originalEmptyClause
      (fun _proofCert originalProof => originalProof)

theorem ay_vrdm_accepted_manifest_sat_sound
    (directoryManifest artifactPaths certificateDigests checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch modelCertificate originalModel : Prop) :
    ay_vrdm_directory_contract directoryManifest artifactPaths
      certificateDigests checkerTranscript solverBuildConfig
      originalFormulaFingerprint reconstructionMap fallbackBranch ->
    modelCertificate -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vrdm_accepted_manifest_unsat_sound
    (directoryManifest artifactPaths certificateDigests checkerTranscript
      solverBuildConfig originalFormulaFingerprint reconstructionMap
      fallbackBranch proofCertificate originalEmptyClause : Prop) :
    ay_vrdm_directory_contract directoryManifest artifactPaths
      certificateDigests checkerTranscript solverBuildConfig
      originalFormulaFingerprint reconstructionMap fallbackBranch ->
    proofCertificate -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofCert originalProof => originalProof

theorem ay_vrdm_no_claim_intro
    (reason fallbackBranch auditTrail : Prop) :
    reason -> fallbackBranch -> auditTrail ->
    ay_vrdm_no_claim reason fallbackBranch auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vrdm_conj_intro reason
      (ay_vrdm_conj fallbackBranch auditTrail)
      reasonProof
      (ay_vrdm_conj_intro fallbackBranch auditTrail
        fallbackProof auditProof)

theorem ay_vrdm_no_claim_reason
    (reason fallbackBranch auditTrail : Prop) :
    ay_vrdm_no_claim reason fallbackBranch auditTrail -> reason :=
  fun noClaim =>
    ay_vrdm_conj_left reason
      (ay_vrdm_conj fallbackBranch auditTrail)
      noClaim

theorem ay_vrdm_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vrdm_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vrdm_conj_intro reason
      (ay_vrdm_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vrdm_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vrdm_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vrdm_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vrdm_conj_right reason
      (ay_vrdm_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vrdm_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vrdm_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vrdm_conj_right reason
      (ay_vrdm_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vrdm_recompute_intro
    (reason fallbackBranch recomputeObligation : Prop) :
    reason -> fallbackBranch -> recomputeObligation ->
    ay_vrdm_recompute reason fallbackBranch recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vrdm_conj_intro reason
      (ay_vrdm_conj fallbackBranch recomputeObligation)
      reasonProof
      (ay_vrdm_conj_intro fallbackBranch recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vrdm_manifest_failure_intro
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vrdm_manifest_failure satFact unsatFact reason fallbackBranch
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vrdm_conj_intro
      (ay_vrdm_blocked_publication satFact unsatFact reason)
      (ay_vrdm_recompute reason fallbackBranch recomputeObligation)
      (ay_vrdm_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vrdm_recompute_intro reason fallbackBranch recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vrdm_manifest_failure_blocks_sat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vrdm_manifest_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vrdm_blocked_publication_no_sat satFact unsatFact reason
      (ay_vrdm_conj_left
        (ay_vrdm_blocked_publication satFact unsatFact reason)
        (ay_vrdm_recompute reason fallbackBranch recomputeObligation)
        failure)

theorem ay_vrdm_manifest_failure_blocks_unsat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vrdm_manifest_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vrdm_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vrdm_conj_left
        (ay_vrdm_blocked_publication satFact unsatFact reason)
        (ay_vrdm_recompute reason fallbackBranch recomputeObligation)
        failure)

theorem ay_vrdm_manifest_failure_recompute
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vrdm_manifest_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    ay_vrdm_recompute reason fallbackBranch recomputeObligation :=
  fun failure =>
    ay_vrdm_conj_right
      (ay_vrdm_blocked_publication satFact unsatFact reason)
      (ay_vrdm_recompute reason fallbackBranch recomputeObligation)
      failure

theorem ay_vrdm_missing_artifact_forces_no_claim
    (satFact unsatFact missingArtifact fallbackBranch
      recomputeObligation : Prop) :
    missingArtifact -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vrdm_manifest_failure satFact unsatFact missingArtifact fallbackBranch
      recomputeObligation :=
  ay_vrdm_manifest_failure_intro satFact unsatFact missingArtifact
    fallbackBranch recomputeObligation

theorem ay_vrdm_moved_artifact_forces_no_claim
    (satFact unsatFact movedArtifact fallbackBranch
      recomputeObligation : Prop) :
    movedArtifact -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vrdm_manifest_failure satFact unsatFact movedArtifact fallbackBranch
      recomputeObligation :=
  ay_vrdm_manifest_failure_intro satFact unsatFact movedArtifact
    fallbackBranch recomputeObligation

theorem ay_vrdm_stale_manifest_cannot_bless_sat
    (satFact unsatFact staleDirectoryManifest fallbackBranch
      recomputeObligation : Prop) :
    ay_vrdm_manifest_failure satFact unsatFact staleDirectoryManifest
      fallbackBranch recomputeObligation ->
    satFact -> False :=
  ay_vrdm_manifest_failure_blocks_sat satFact unsatFact staleDirectoryManifest
    fallbackBranch recomputeObligation

theorem ay_vrdm_stale_manifest_cannot_bless_unsat
    (satFact unsatFact staleDirectoryManifest fallbackBranch
      recomputeObligation : Prop) :
    ay_vrdm_manifest_failure satFact unsatFact staleDirectoryManifest
      fallbackBranch recomputeObligation ->
    unsatFact -> False :=
  ay_vrdm_manifest_failure_blocks_unsat satFact unsatFact
    staleDirectoryManifest fallbackBranch recomputeObligation
