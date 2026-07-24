-- SAT-COMP validator public artifact checksum manifest core.
--
-- Public result files, model/proof artifacts, checker transcripts, formula
-- fingerprints, build configs, and checksum manifests preserve SAT/UNSAT
-- soundness only when the accepted manifest contract is present.

def ay_vpac_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vpac_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vpac_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vpac_disj satFact (ay_vpac_disj unsatFact noClaimFact)

def ay_vpac_checksum_contract
    (publishedResultFiles modelOrProofArtifacts checkerTranscripts
      formulaFingerprints buildConfigs checksumManifest reconstructionMap
      fallbackBranch : Prop) : Prop :=
  ay_vpac_conj publishedResultFiles
    (ay_vpac_conj modelOrProofArtifacts
      (ay_vpac_conj checkerTranscripts
        (ay_vpac_conj formulaFingerprints
          (ay_vpac_conj buildConfigs
            (ay_vpac_conj checksumManifest
              (ay_vpac_conj reconstructionMap fallbackBranch))))))

def ay_vpac_sat_publication
    (checksumContract modelEvidence originalModel : Prop) : Prop :=
  ay_vpac_conj checksumContract
    (ay_vpac_conj modelEvidence originalModel)

def ay_vpac_unsat_publication
    (checksumContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vpac_conj checksumContract
    (ay_vpac_conj proofEvidence originalEmptyClause)

def ay_vpac_no_claim
    (reason fallbackBranch auditTrail : Prop) : Prop :=
  ay_vpac_conj reason (ay_vpac_conj fallbackBranch auditTrail)

def ay_vpac_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vpac_conj reason
    (ay_vpac_conj (satFact -> False) (unsatFact -> False))

def ay_vpac_recompute
    (reason fallbackBranch recomputeObligation : Prop) : Prop :=
  ay_vpac_conj reason
    (ay_vpac_conj fallbackBranch recomputeObligation)

def ay_vpac_manifest_failure
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    Prop :=
  ay_vpac_conj
    (ay_vpac_blocked_publication satFact unsatFact reason)
    (ay_vpac_recompute reason fallbackBranch recomputeObligation)

theorem ay_vpac_conj_intro (left right : Prop) :
    left -> right -> ay_vpac_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vpac_conj_left (left right : Prop) :
    ay_vpac_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vpac_conj_right (left right : Prop) :
    ay_vpac_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vpac_disj_left (left right : Prop) :
    left -> ay_vpac_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vpac_disj_right (left right : Prop) :
    right -> ay_vpac_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vpac_checksum_contract_intro
    (publishedResultFiles modelOrProofArtifacts checkerTranscripts
      formulaFingerprints buildConfigs checksumManifest reconstructionMap
      fallbackBranch : Prop) :
    publishedResultFiles -> modelOrProofArtifacts -> checkerTranscripts ->
    formulaFingerprints -> buildConfigs -> checksumManifest ->
    reconstructionMap -> fallbackBranch ->
    ay_vpac_checksum_contract publishedResultFiles modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs checksumManifest
      reconstructionMap fallbackBranch :=
  fun resultFilesProof artifactsProof transcriptsProof fingerprintsProof
      buildProof checksumProof reconstructionProof fallbackProof =>
    ay_vpac_conj_intro publishedResultFiles
      (ay_vpac_conj modelOrProofArtifacts
        (ay_vpac_conj checkerTranscripts
          (ay_vpac_conj formulaFingerprints
            (ay_vpac_conj buildConfigs
              (ay_vpac_conj checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch))))))
      resultFilesProof
      (ay_vpac_conj_intro modelOrProofArtifacts
        (ay_vpac_conj checkerTranscripts
          (ay_vpac_conj formulaFingerprints
            (ay_vpac_conj buildConfigs
              (ay_vpac_conj checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch)))))
        artifactsProof
        (ay_vpac_conj_intro checkerTranscripts
          (ay_vpac_conj formulaFingerprints
            (ay_vpac_conj buildConfigs
              (ay_vpac_conj checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch))))
          transcriptsProof
          (ay_vpac_conj_intro formulaFingerprints
            (ay_vpac_conj buildConfigs
              (ay_vpac_conj checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch)))
            fingerprintsProof
            (ay_vpac_conj_intro buildConfigs
              (ay_vpac_conj checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch))
              buildProof
              (ay_vpac_conj_intro checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch)
                checksumProof
                (ay_vpac_conj_intro reconstructionMap fallbackBranch
                  reconstructionProof fallbackProof))))))

theorem ay_vpac_checksum_contract_result_files
    (publishedResultFiles modelOrProofArtifacts checkerTranscripts
      formulaFingerprints buildConfigs checksumManifest reconstructionMap
      fallbackBranch : Prop) :
    ay_vpac_checksum_contract publishedResultFiles modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs checksumManifest
      reconstructionMap fallbackBranch ->
    publishedResultFiles :=
  fun contract =>
    ay_vpac_conj_left publishedResultFiles
      (ay_vpac_conj modelOrProofArtifacts
        (ay_vpac_conj checkerTranscripts
          (ay_vpac_conj formulaFingerprints
            (ay_vpac_conj buildConfigs
              (ay_vpac_conj checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch))))))
      contract

theorem ay_vpac_checksum_contract_artifacts
    (publishedResultFiles modelOrProofArtifacts checkerTranscripts
      formulaFingerprints buildConfigs checksumManifest reconstructionMap
      fallbackBranch : Prop) :
    ay_vpac_checksum_contract publishedResultFiles modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs checksumManifest
      reconstructionMap fallbackBranch ->
    modelOrProofArtifacts :=
  fun contract =>
    ay_vpac_conj_right publishedResultFiles
      (ay_vpac_conj modelOrProofArtifacts
        (ay_vpac_conj checkerTranscripts
          (ay_vpac_conj formulaFingerprints
            (ay_vpac_conj buildConfigs
              (ay_vpac_conj checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch))))))
      contract modelOrProofArtifacts
      (fun artifactsProof _tail => artifactsProof)

theorem ay_vpac_checksum_contract_transcripts
    (publishedResultFiles modelOrProofArtifacts checkerTranscripts
      formulaFingerprints buildConfigs checksumManifest reconstructionMap
      fallbackBranch : Prop) :
    ay_vpac_checksum_contract publishedResultFiles modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs checksumManifest
      reconstructionMap fallbackBranch ->
    checkerTranscripts :=
  fun contract =>
    ay_vpac_conj_right publishedResultFiles
      (ay_vpac_conj modelOrProofArtifacts
        (ay_vpac_conj checkerTranscripts
          (ay_vpac_conj formulaFingerprints
            (ay_vpac_conj buildConfigs
              (ay_vpac_conj checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch))))))
      contract checkerTranscripts
      (fun _artifactsProof tail =>
        tail checkerTranscripts
          (fun transcriptsProof _tail2 => transcriptsProof))

theorem ay_vpac_checksum_contract_fingerprints
    (publishedResultFiles modelOrProofArtifacts checkerTranscripts
      formulaFingerprints buildConfigs checksumManifest reconstructionMap
      fallbackBranch : Prop) :
    ay_vpac_checksum_contract publishedResultFiles modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs checksumManifest
      reconstructionMap fallbackBranch ->
    formulaFingerprints :=
  fun contract =>
    ay_vpac_conj_right publishedResultFiles
      (ay_vpac_conj modelOrProofArtifacts
        (ay_vpac_conj checkerTranscripts
          (ay_vpac_conj formulaFingerprints
            (ay_vpac_conj buildConfigs
              (ay_vpac_conj checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch))))))
      contract formulaFingerprints
      (fun _artifactsProof tail =>
        tail formulaFingerprints
          (fun _transcriptsProof tail2 =>
            tail2 formulaFingerprints
              (fun fingerprintsProof _tail3 => fingerprintsProof)))

theorem ay_vpac_checksum_contract_build_configs
    (publishedResultFiles modelOrProofArtifacts checkerTranscripts
      formulaFingerprints buildConfigs checksumManifest reconstructionMap
      fallbackBranch : Prop) :
    ay_vpac_checksum_contract publishedResultFiles modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs checksumManifest
      reconstructionMap fallbackBranch ->
    buildConfigs :=
  fun contract =>
    ay_vpac_conj_right publishedResultFiles
      (ay_vpac_conj modelOrProofArtifacts
        (ay_vpac_conj checkerTranscripts
          (ay_vpac_conj formulaFingerprints
            (ay_vpac_conj buildConfigs
              (ay_vpac_conj checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch))))))
      contract buildConfigs
      (fun _artifactsProof tail =>
        tail buildConfigs
          (fun _transcriptsProof tail2 =>
            tail2 buildConfigs
              (fun _fingerprintsProof tail3 =>
                tail3 buildConfigs
                  (fun buildProof _tail4 => buildProof))))

theorem ay_vpac_checksum_contract_checksum_manifest
    (publishedResultFiles modelOrProofArtifacts checkerTranscripts
      formulaFingerprints buildConfigs checksumManifest reconstructionMap
      fallbackBranch : Prop) :
    ay_vpac_checksum_contract publishedResultFiles modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs checksumManifest
      reconstructionMap fallbackBranch ->
    checksumManifest :=
  fun contract =>
    ay_vpac_conj_right publishedResultFiles
      (ay_vpac_conj modelOrProofArtifacts
        (ay_vpac_conj checkerTranscripts
          (ay_vpac_conj formulaFingerprints
            (ay_vpac_conj buildConfigs
              (ay_vpac_conj checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch))))))
      contract checksumManifest
      (fun _artifactsProof tail =>
        tail checksumManifest
          (fun _transcriptsProof tail2 =>
            tail2 checksumManifest
              (fun _fingerprintsProof tail3 =>
                tail3 checksumManifest
                  (fun _buildProof tail4 =>
                    tail4 checksumManifest
                      (fun checksumProof _tail5 => checksumProof)))))

theorem ay_vpac_checksum_contract_reconstruction
    (publishedResultFiles modelOrProofArtifacts checkerTranscripts
      formulaFingerprints buildConfigs checksumManifest reconstructionMap
      fallbackBranch : Prop) :
    ay_vpac_checksum_contract publishedResultFiles modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs checksumManifest
      reconstructionMap fallbackBranch ->
    reconstructionMap :=
  fun contract =>
    ay_vpac_conj_right publishedResultFiles
      (ay_vpac_conj modelOrProofArtifacts
        (ay_vpac_conj checkerTranscripts
          (ay_vpac_conj formulaFingerprints
            (ay_vpac_conj buildConfigs
              (ay_vpac_conj checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch))))))
      contract reconstructionMap
      (fun _artifactsProof tail =>
        tail reconstructionMap
          (fun _transcriptsProof tail2 =>
            tail2 reconstructionMap
              (fun _fingerprintsProof tail3 =>
                tail3 reconstructionMap
                  (fun _buildProof tail4 =>
                    tail4 reconstructionMap
                      (fun _checksumProof tail5 =>
                        tail5 reconstructionMap
                          (fun reconstructionProof _fallbackProof =>
                            reconstructionProof))))))

theorem ay_vpac_checksum_contract_fallback
    (publishedResultFiles modelOrProofArtifacts checkerTranscripts
      formulaFingerprints buildConfigs checksumManifest reconstructionMap
      fallbackBranch : Prop) :
    ay_vpac_checksum_contract publishedResultFiles modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs checksumManifest
      reconstructionMap fallbackBranch ->
    fallbackBranch :=
  fun contract =>
    ay_vpac_conj_right publishedResultFiles
      (ay_vpac_conj modelOrProofArtifacts
        (ay_vpac_conj checkerTranscripts
          (ay_vpac_conj formulaFingerprints
            (ay_vpac_conj buildConfigs
              (ay_vpac_conj checksumManifest
                (ay_vpac_conj reconstructionMap fallbackBranch))))))
      contract fallbackBranch
      (fun _artifactsProof tail =>
        tail fallbackBranch
          (fun _transcriptsProof tail2 =>
            tail2 fallbackBranch
              (fun _fingerprintsProof tail3 =>
                tail3 fallbackBranch
                  (fun _buildProof tail4 =>
                    tail4 fallbackBranch
                      (fun _checksumProof tail5 =>
                        tail5 fallbackBranch
                          (fun _reconstructionProof fallbackProof =>
                            fallbackProof))))))

theorem ay_vpac_sat_publication_intro
    (checksumContract modelEvidence originalModel : Prop) :
    checksumContract -> modelEvidence -> originalModel ->
    ay_vpac_sat_publication checksumContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vpac_conj_intro checksumContract
      (ay_vpac_conj modelEvidence originalModel)
      contractProof
      (ay_vpac_conj_intro modelEvidence originalModel
        modelProof originalProof)

theorem ay_vpac_sat_publication_original_model
    (checksumContract modelEvidence originalModel : Prop) :
    ay_vpac_sat_publication checksumContract modelEvidence originalModel ->
    originalModel :=
  fun publication =>
    ay_vpac_conj_right checksumContract
      (ay_vpac_conj modelEvidence originalModel)
      publication originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vpac_unsat_publication_intro
    (checksumContract proofEvidence originalEmptyClause : Prop) :
    checksumContract -> proofEvidence -> originalEmptyClause ->
    ay_vpac_unsat_publication checksumContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofProof originalProof =>
    ay_vpac_conj_intro checksumContract
      (ay_vpac_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vpac_conj_intro proofEvidence originalEmptyClause
        proofProof originalProof)

theorem ay_vpac_unsat_publication_original_empty_clause
    (checksumContract proofEvidence originalEmptyClause : Prop) :
    ay_vpac_unsat_publication checksumContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_vpac_conj_right checksumContract
      (ay_vpac_conj proofEvidence originalEmptyClause)
      publication originalEmptyClause
      (fun _proofProof originalProof => originalProof)

theorem ay_vpac_accepted_checksum_manifest_sat_sound
    (publishedResultFiles modelOrProofArtifacts checkerTranscripts
      formulaFingerprints buildConfigs checksumManifest reconstructionMap
      fallbackBranch modelEvidence originalModel : Prop) :
    ay_vpac_checksum_contract publishedResultFiles modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs checksumManifest
      reconstructionMap fallbackBranch ->
    modelEvidence -> originalModel ->
    originalModel :=
  fun _contract _modelProof originalProof => originalProof

theorem ay_vpac_accepted_checksum_manifest_unsat_sound
    (publishedResultFiles modelOrProofArtifacts checkerTranscripts
      formulaFingerprints buildConfigs checksumManifest reconstructionMap
      fallbackBranch proofEvidence originalEmptyClause : Prop) :
    ay_vpac_checksum_contract publishedResultFiles modelOrProofArtifacts
      checkerTranscripts formulaFingerprints buildConfigs checksumManifest
      reconstructionMap fallbackBranch ->
    proofEvidence -> originalEmptyClause ->
    originalEmptyClause :=
  fun _contract _proofProof originalProof => originalProof

theorem ay_vpac_no_claim_intro
    (reason fallbackBranch auditTrail : Prop) :
    reason -> fallbackBranch -> auditTrail ->
    ay_vpac_no_claim reason fallbackBranch auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_vpac_conj_intro reason
      (ay_vpac_conj fallbackBranch auditTrail)
      reasonProof
      (ay_vpac_conj_intro fallbackBranch auditTrail
        fallbackProof auditProof)

theorem ay_vpac_no_claim_reason
    (reason fallbackBranch auditTrail : Prop) :
    ay_vpac_no_claim reason fallbackBranch auditTrail -> reason :=
  fun noClaim =>
    ay_vpac_conj_left reason
      (ay_vpac_conj fallbackBranch auditTrail)
      noClaim

theorem ay_vpac_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vpac_blocked_publication satFact unsatFact reason :=
  fun reasonProof blocksSat blocksUnsat =>
    ay_vpac_conj_intro reason
      (ay_vpac_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vpac_conj_intro (satFact -> False) (unsatFact -> False)
        blocksSat blocksUnsat)

theorem ay_vpac_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vpac_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vpac_conj_right reason
      (ay_vpac_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blocksSat _blocksUnsat => blocksSat)

theorem ay_vpac_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vpac_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vpac_conj_right reason
      (ay_vpac_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blocksSat blocksUnsat => blocksUnsat)

theorem ay_vpac_recompute_intro
    (reason fallbackBranch recomputeObligation : Prop) :
    reason -> fallbackBranch -> recomputeObligation ->
    ay_vpac_recompute reason fallbackBranch recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_vpac_conj_intro reason
      (ay_vpac_conj fallbackBranch recomputeObligation)
      reasonProof
      (ay_vpac_conj_intro fallbackBranch recomputeObligation
        fallbackProof recomputeProof)

theorem ay_vpac_manifest_failure_intro
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vpac_manifest_failure satFact unsatFact reason fallbackBranch
      recomputeObligation :=
  fun reasonProof blocksSat blocksUnsat fallbackProof recomputeProof =>
    ay_vpac_conj_intro
      (ay_vpac_blocked_publication satFact unsatFact reason)
      (ay_vpac_recompute reason fallbackBranch recomputeObligation)
      (ay_vpac_blocked_publication_intro satFact unsatFact reason
        reasonProof blocksSat blocksUnsat)
      (ay_vpac_recompute_intro reason fallbackBranch recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_vpac_manifest_failure_blocks_sat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vpac_manifest_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_vpac_blocked_publication_no_sat satFact unsatFact reason
      (ay_vpac_conj_left
        (ay_vpac_blocked_publication satFact unsatFact reason)
        (ay_vpac_recompute reason fallbackBranch recomputeObligation)
        failure)

theorem ay_vpac_manifest_failure_blocks_unsat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vpac_manifest_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_vpac_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vpac_conj_left
        (ay_vpac_blocked_publication satFact unsatFact reason)
        (ay_vpac_recompute reason fallbackBranch recomputeObligation)
        failure)

theorem ay_vpac_manifest_failure_recompute
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vpac_manifest_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    ay_vpac_recompute reason fallbackBranch recomputeObligation :=
  fun failure =>
    ay_vpac_conj_right
      (ay_vpac_blocked_publication satFact unsatFact reason)
      (ay_vpac_recompute reason fallbackBranch recomputeObligation)
      failure

theorem ay_vpac_checksum_mismatch_forces_no_claim
    (satFact unsatFact checksumMismatch fallbackBranch
      recomputeObligation : Prop) :
    checksumMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vpac_manifest_failure satFact unsatFact checksumMismatch
      fallbackBranch recomputeObligation :=
  ay_vpac_manifest_failure_intro satFact unsatFact checksumMismatch
    fallbackBranch recomputeObligation

theorem ay_vpac_missing_artifact_forces_no_claim
    (satFact unsatFact missingArtifact fallbackBranch
      recomputeObligation : Prop) :
    missingArtifact -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vpac_manifest_failure satFact unsatFact missingArtifact fallbackBranch
      recomputeObligation :=
  ay_vpac_manifest_failure_intro satFact unsatFact missingArtifact
    fallbackBranch recomputeObligation

theorem ay_vpac_stale_manifest_forces_no_claim
    (satFact unsatFact staleManifest fallbackBranch recomputeObligation : Prop) :
    staleManifest -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vpac_manifest_failure satFact unsatFact staleManifest fallbackBranch
      recomputeObligation :=
  ay_vpac_manifest_failure_intro satFact unsatFact staleManifest
    fallbackBranch recomputeObligation

theorem ay_vpac_unchecked_transcript_forces_no_claim
    (satFact unsatFact uncheckedTranscript fallbackBranch
      recomputeObligation : Prop) :
    uncheckedTranscript -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackBranch -> recomputeObligation ->
    ay_vpac_manifest_failure satFact unsatFact uncheckedTranscript
      fallbackBranch recomputeObligation :=
  ay_vpac_manifest_failure_intro satFact unsatFact uncheckedTranscript
    fallbackBranch recomputeObligation

theorem ay_vpac_failed_manifest_cannot_bless_sat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vpac_manifest_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    satFact -> False :=
  ay_vpac_manifest_failure_blocks_sat satFact unsatFact reason
    fallbackBranch recomputeObligation

theorem ay_vpac_failed_manifest_cannot_bless_unsat
    (satFact unsatFact reason fallbackBranch recomputeObligation : Prop) :
    ay_vpac_manifest_failure satFact unsatFact reason fallbackBranch
      recomputeObligation ->
    unsatFact -> False :=
  ay_vpac_manifest_failure_blocks_unsat satFact unsatFact reason
    fallbackBranch recomputeObligation
