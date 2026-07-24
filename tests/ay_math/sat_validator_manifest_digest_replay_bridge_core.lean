-- SAT-COMP validator manifest/digest/replay bridge core.
--
-- A proof or model replay is trusted only when manifest membership, digest
-- root, replay transcript, formula fingerprint, preprocessing reconstruction,
-- and exit-code contract all bridge to the same public result.  Stale or
-- mismatched bridge data produces no-claim/recompute instead of publication.

def ay_vmdb_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vmdb_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vmdb_equisat (before after : Prop) : Prop :=
  ay_vmdb_conj (before -> after) (after -> before)

def ay_vmdb_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vmdb_disj satFact (ay_vmdb_disj unsatFact noClaimFact)

def ay_vmdb_bridge_contract
    (manifestMembership digestRoot replayTranscript formulaFingerprint
      preprocessReconstruction exitCodeContract : Prop) : Prop :=
  ay_vmdb_conj manifestMembership
    (ay_vmdb_conj digestRoot
      (ay_vmdb_conj replayTranscript
        (ay_vmdb_conj formulaFingerprint
          (ay_vmdb_conj preprocessReconstruction exitCodeContract))))

def ay_vmdb_sat_bridge
    (bridgeContract modelReplay originalModel : Prop) : Prop :=
  ay_vmdb_conj bridgeContract (ay_vmdb_conj modelReplay originalModel)

def ay_vmdb_unsat_bridge
    (bridgeContract proofReplay originalEmptyClause : Prop) : Prop :=
  ay_vmdb_conj bridgeContract
    (ay_vmdb_conj proofReplay originalEmptyClause)

def ay_vmdb_no_claim
    (reason auditDigest diagnostic : Prop) : Prop :=
  ay_vmdb_conj reason (ay_vmdb_conj auditDigest diagnostic)

def ay_vmdb_recompute
    (reason bridgeAudit diagnostic : Prop) : Prop :=
  ay_vmdb_conj reason (ay_vmdb_conj bridgeAudit diagnostic)

def ay_vmdb_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vmdb_conj reason
    (ay_vmdb_conj (satFact -> False) (unsatFact -> False))

def ay_vmdb_failure
    (satFact unsatFact reason bridgeAudit diagnostic : Prop) : Prop :=
  ay_vmdb_conj
    (ay_vmdb_blocked_publication satFact unsatFact reason)
    (ay_vmdb_recompute reason bridgeAudit diagnostic)

def ay_vmdb_model (formula assignment : Prop) : Prop :=
  ay_vmdb_conj formula assignment

def ay_vmdb_unsat (formula : Prop) : Prop :=
  formula -> False

def ay_vmdb_preprocess_bridge (original solver : Prop) : Prop :=
  ay_vmdb_equisat original solver

theorem ay_vmdb_conj_intro (left right : Prop) :
    left -> right -> ay_vmdb_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vmdb_conj_left (left right : Prop) :
    ay_vmdb_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vmdb_conj_right (left right : Prop) :
    ay_vmdb_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vmdb_disj_left (left right : Prop) :
    left -> ay_vmdb_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vmdb_disj_right (left right : Prop) :
    right -> ay_vmdb_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vmdb_equisat_forward (before after : Prop) :
    ay_vmdb_equisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vmdb_equisat_backward (before after : Prop) :
    ay_vmdb_equisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vmdb_model_intro (formula assignment : Prop) :
    formula -> assignment -> ay_vmdb_model formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vmdb_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vmdb_model_formula (formula assignment : Prop) :
    ay_vmdb_model formula assignment -> formula :=
  fun model => ay_vmdb_conj_left formula assignment model

theorem ay_vmdb_model_assignment (formula assignment : Prop) :
    ay_vmdb_model formula assignment -> assignment :=
  fun model => ay_vmdb_conj_right formula assignment model

theorem ay_vmdb_bridge_contract_intro
    (manifestMembership digestRoot replayTranscript formulaFingerprint
      preprocessReconstruction exitCodeContract : Prop) :
    manifestMembership -> digestRoot -> replayTranscript ->
    formulaFingerprint -> preprocessReconstruction -> exitCodeContract ->
    ay_vmdb_bridge_contract manifestMembership digestRoot replayTranscript
      formulaFingerprint preprocessReconstruction exitCodeContract :=
  fun membershipProof digestProof transcriptProof fingerprintProof
      reconstructionProof exitProof =>
    ay_vmdb_conj_intro manifestMembership
      (ay_vmdb_conj digestRoot
        (ay_vmdb_conj replayTranscript
          (ay_vmdb_conj formulaFingerprint
            (ay_vmdb_conj preprocessReconstruction exitCodeContract))))
      membershipProof
      (ay_vmdb_conj_intro digestRoot
        (ay_vmdb_conj replayTranscript
          (ay_vmdb_conj formulaFingerprint
            (ay_vmdb_conj preprocessReconstruction exitCodeContract)))
        digestProof
        (ay_vmdb_conj_intro replayTranscript
          (ay_vmdb_conj formulaFingerprint
            (ay_vmdb_conj preprocessReconstruction exitCodeContract))
          transcriptProof
          (ay_vmdb_conj_intro formulaFingerprint
            (ay_vmdb_conj preprocessReconstruction exitCodeContract)
            fingerprintProof
            (ay_vmdb_conj_intro preprocessReconstruction exitCodeContract
              reconstructionProof exitProof))))

theorem ay_vmdb_bridge_contract_membership
    (manifestMembership digestRoot replayTranscript formulaFingerprint
      preprocessReconstruction exitCodeContract : Prop) :
    ay_vmdb_bridge_contract manifestMembership digestRoot replayTranscript
      formulaFingerprint preprocessReconstruction exitCodeContract ->
    manifestMembership :=
  fun contract =>
    ay_vmdb_conj_left manifestMembership
      (ay_vmdb_conj digestRoot
        (ay_vmdb_conj replayTranscript
          (ay_vmdb_conj formulaFingerprint
            (ay_vmdb_conj preprocessReconstruction exitCodeContract))))
      contract

theorem ay_vmdb_bridge_contract_digest
    (manifestMembership digestRoot replayTranscript formulaFingerprint
      preprocessReconstruction exitCodeContract : Prop) :
    ay_vmdb_bridge_contract manifestMembership digestRoot replayTranscript
      formulaFingerprint preprocessReconstruction exitCodeContract ->
    digestRoot :=
  fun contract =>
    ay_vmdb_conj_right manifestMembership
      (ay_vmdb_conj digestRoot
        (ay_vmdb_conj replayTranscript
          (ay_vmdb_conj formulaFingerprint
            (ay_vmdb_conj preprocessReconstruction exitCodeContract))))
      contract digestRoot
      (fun digestProof _tail => digestProof)

theorem ay_vmdb_bridge_contract_transcript
    (manifestMembership digestRoot replayTranscript formulaFingerprint
      preprocessReconstruction exitCodeContract : Prop) :
    ay_vmdb_bridge_contract manifestMembership digestRoot replayTranscript
      formulaFingerprint preprocessReconstruction exitCodeContract ->
    replayTranscript :=
  fun contract =>
    ay_vmdb_conj_right manifestMembership
      (ay_vmdb_conj digestRoot
        (ay_vmdb_conj replayTranscript
          (ay_vmdb_conj formulaFingerprint
            (ay_vmdb_conj preprocessReconstruction exitCodeContract))))
      contract replayTranscript
      (fun _digestProof tail =>
        tail replayTranscript (fun transcriptProof _tail2 => transcriptProof))

theorem ay_vmdb_bridge_contract_fingerprint
    (manifestMembership digestRoot replayTranscript formulaFingerprint
      preprocessReconstruction exitCodeContract : Prop) :
    ay_vmdb_bridge_contract manifestMembership digestRoot replayTranscript
      formulaFingerprint preprocessReconstruction exitCodeContract ->
    formulaFingerprint :=
  fun contract =>
    ay_vmdb_conj_right manifestMembership
      (ay_vmdb_conj digestRoot
        (ay_vmdb_conj replayTranscript
          (ay_vmdb_conj formulaFingerprint
            (ay_vmdb_conj preprocessReconstruction exitCodeContract))))
      contract formulaFingerprint
      (fun _digestProof tail =>
        tail formulaFingerprint
          (fun _transcriptProof tail2 =>
            tail2 formulaFingerprint
              (fun fingerprintProof _tail3 => fingerprintProof)))

theorem ay_vmdb_bridge_contract_reconstruction
    (manifestMembership digestRoot replayTranscript formulaFingerprint
      preprocessReconstruction exitCodeContract : Prop) :
    ay_vmdb_bridge_contract manifestMembership digestRoot replayTranscript
      formulaFingerprint preprocessReconstruction exitCodeContract ->
    preprocessReconstruction :=
  fun contract =>
    ay_vmdb_conj_right manifestMembership
      (ay_vmdb_conj digestRoot
        (ay_vmdb_conj replayTranscript
          (ay_vmdb_conj formulaFingerprint
            (ay_vmdb_conj preprocessReconstruction exitCodeContract))))
      contract preprocessReconstruction
      (fun _digestProof tail =>
        tail preprocessReconstruction
          (fun _transcriptProof tail2 =>
            tail2 preprocessReconstruction
              (fun _fingerprintProof tail3 =>
                tail3 preprocessReconstruction
                  (fun reconstructionProof _exitProof =>
                    reconstructionProof))))

theorem ay_vmdb_bridge_contract_exit
    (manifestMembership digestRoot replayTranscript formulaFingerprint
      preprocessReconstruction exitCodeContract : Prop) :
    ay_vmdb_bridge_contract manifestMembership digestRoot replayTranscript
      formulaFingerprint preprocessReconstruction exitCodeContract ->
    exitCodeContract :=
  fun contract =>
    ay_vmdb_conj_right manifestMembership
      (ay_vmdb_conj digestRoot
        (ay_vmdb_conj replayTranscript
          (ay_vmdb_conj formulaFingerprint
            (ay_vmdb_conj preprocessReconstruction exitCodeContract))))
      contract exitCodeContract
      (fun _digestProof tail =>
        tail exitCodeContract
          (fun _transcriptProof tail2 =>
            tail2 exitCodeContract
              (fun _fingerprintProof tail3 =>
                tail3 exitCodeContract
                  (fun _reconstructionProof exitProof => exitProof))))

theorem ay_vmdb_sat_bridge_intro
    (bridgeContract modelReplay originalModel : Prop) :
    bridgeContract -> modelReplay -> originalModel ->
    ay_vmdb_sat_bridge bridgeContract modelReplay originalModel :=
  fun contractProof replayProof modelProof =>
    ay_vmdb_conj_intro bridgeContract
      (ay_vmdb_conj modelReplay originalModel)
      contractProof
      (ay_vmdb_conj_intro modelReplay originalModel replayProof modelProof)

theorem ay_vmdb_sat_bridge_contract
    (bridgeContract modelReplay originalModel : Prop) :
    ay_vmdb_sat_bridge bridgeContract modelReplay originalModel ->
    bridgeContract :=
  fun bridge =>
    ay_vmdb_conj_left bridgeContract
      (ay_vmdb_conj modelReplay originalModel) bridge

theorem ay_vmdb_sat_bridge_model_replay
    (bridgeContract modelReplay originalModel : Prop) :
    ay_vmdb_sat_bridge bridgeContract modelReplay originalModel ->
    modelReplay :=
  fun bridge =>
    ay_vmdb_conj_right bridgeContract
      (ay_vmdb_conj modelReplay originalModel)
      bridge modelReplay
      (fun replayProof _modelProof => replayProof)

theorem ay_vmdb_sat_bridge_original_model
    (bridgeContract modelReplay originalModel : Prop) :
    ay_vmdb_sat_bridge bridgeContract modelReplay originalModel ->
    originalModel :=
  fun bridge =>
    ay_vmdb_conj_right bridgeContract
      (ay_vmdb_conj modelReplay originalModel)
      bridge originalModel
      (fun _replayProof modelProof => modelProof)

theorem ay_vmdb_unsat_bridge_intro
    (bridgeContract proofReplay originalEmptyClause : Prop) :
    bridgeContract -> proofReplay -> originalEmptyClause ->
    ay_vmdb_unsat_bridge bridgeContract proofReplay originalEmptyClause :=
  fun contractProof replayProof emptyClauseProof =>
    ay_vmdb_conj_intro bridgeContract
      (ay_vmdb_conj proofReplay originalEmptyClause)
      contractProof
      (ay_vmdb_conj_intro proofReplay originalEmptyClause replayProof
        emptyClauseProof)

theorem ay_vmdb_unsat_bridge_contract
    (bridgeContract proofReplay originalEmptyClause : Prop) :
    ay_vmdb_unsat_bridge bridgeContract proofReplay originalEmptyClause ->
    bridgeContract :=
  fun bridge =>
    ay_vmdb_conj_left bridgeContract
      (ay_vmdb_conj proofReplay originalEmptyClause) bridge

theorem ay_vmdb_unsat_bridge_proof_replay
    (bridgeContract proofReplay originalEmptyClause : Prop) :
    ay_vmdb_unsat_bridge bridgeContract proofReplay originalEmptyClause ->
    proofReplay :=
  fun bridge =>
    ay_vmdb_conj_right bridgeContract
      (ay_vmdb_conj proofReplay originalEmptyClause)
      bridge proofReplay
      (fun replayProof _emptyClauseProof => replayProof)

theorem ay_vmdb_unsat_bridge_original_empty_clause
    (bridgeContract proofReplay originalEmptyClause : Prop) :
    ay_vmdb_unsat_bridge bridgeContract proofReplay originalEmptyClause ->
    originalEmptyClause :=
  fun bridge =>
    ay_vmdb_conj_right bridgeContract
      (ay_vmdb_conj proofReplay originalEmptyClause)
      bridge originalEmptyClause
      (fun _replayProof emptyClauseProof => emptyClauseProof)

theorem ay_vmdb_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    ay_vmdb_no_claim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vmdb_conj_intro reason
      (ay_vmdb_conj auditDigest diagnostic)
      reasonProof
      (ay_vmdb_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vmdb_recompute_intro
    (reason bridgeAudit diagnostic : Prop) :
    reason -> bridgeAudit -> diagnostic ->
    ay_vmdb_recompute reason bridgeAudit diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vmdb_conj_intro reason
      (ay_vmdb_conj bridgeAudit diagnostic)
      reasonProof
      (ay_vmdb_conj_intro bridgeAudit diagnostic auditProof
        diagnosticProof)

theorem ay_vmdb_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vmdb_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vmdb_conj_intro reason
      (ay_vmdb_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vmdb_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vmdb_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vmdb_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vmdb_conj_right reason
      (ay_vmdb_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vmdb_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vmdb_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vmdb_conj_right reason
      (ay_vmdb_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vmdb_failure_intro
    (satFact unsatFact reason bridgeAudit diagnostic : Prop) :
    ay_vmdb_blocked_publication satFact unsatFact reason ->
    ay_vmdb_recompute reason bridgeAudit diagnostic ->
    ay_vmdb_failure satFact unsatFact reason bridgeAudit diagnostic :=
  fun blocked recompute =>
    ay_vmdb_conj_intro
      (ay_vmdb_blocked_publication satFact unsatFact reason)
      (ay_vmdb_recompute reason bridgeAudit diagnostic)
      blocked recompute

theorem ay_vmdb_failure_blocks_sat
    (satFact unsatFact reason bridgeAudit diagnostic : Prop) :
    ay_vmdb_failure satFact unsatFact reason bridgeAudit diagnostic ->
    satFact -> False :=
  fun failure =>
    ay_vmdb_blocked_publication_no_sat satFact unsatFact reason
      (ay_vmdb_conj_left
        (ay_vmdb_blocked_publication satFact unsatFact reason)
        (ay_vmdb_recompute reason bridgeAudit diagnostic)
        failure)

theorem ay_vmdb_failure_blocks_unsat
    (satFact unsatFact reason bridgeAudit diagnostic : Prop) :
    ay_vmdb_failure satFact unsatFact reason bridgeAudit diagnostic ->
    unsatFact -> False :=
  fun failure =>
    ay_vmdb_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vmdb_conj_left
        (ay_vmdb_blocked_publication satFact unsatFact reason)
        (ay_vmdb_recompute reason bridgeAudit diagnostic)
        failure)

theorem ay_vmdb_failure_recompute
    (satFact unsatFact reason bridgeAudit diagnostic : Prop) :
    ay_vmdb_failure satFact unsatFact reason bridgeAudit diagnostic ->
    ay_vmdb_recompute reason bridgeAudit diagnostic :=
  fun failure =>
    ay_vmdb_conj_right
      (ay_vmdb_blocked_publication satFact unsatFact reason)
      (ay_vmdb_recompute reason bridgeAudit diagnostic)
      failure

theorem ay_vmdb_preprocess_model_reconstruct
    (original solver assignment : Prop) :
    ay_vmdb_preprocess_bridge original solver ->
    ay_vmdb_model solver assignment ->
    ay_vmdb_model original assignment :=
  fun bridge solverModel =>
    ay_vmdb_model_intro original assignment
      (ay_vmdb_equisat_backward original solver bridge
        (ay_vmdb_model_formula solver assignment solverModel))
      (ay_vmdb_model_assignment solver assignment solverModel)

theorem ay_vmdb_preprocess_unsat_reconstruct
    (original solver : Prop) :
    ay_vmdb_preprocess_bridge original solver ->
    ay_vmdb_unsat solver ->
    ay_vmdb_unsat original :=
  fun bridge solverUnsat originalProof =>
    solverUnsat
      (ay_vmdb_equisat_forward original solver bridge originalProof)

theorem ay_vmdb_accepted_sat_bridge_preserves_publication
    (bridgeContract modelReplay originalModel unsatFact noClaimFact : Prop) :
    ay_vmdb_sat_bridge bridgeContract modelReplay originalModel ->
    ay_vmdb_public_result originalModel unsatFact noClaimFact :=
  fun bridge =>
    ay_vmdb_disj_left originalModel
      (ay_vmdb_disj unsatFact noClaimFact)
      (ay_vmdb_sat_bridge_original_model bridgeContract modelReplay
        originalModel bridge)

theorem ay_vmdb_accepted_unsat_bridge_preserves_publication
    (satFact bridgeContract proofReplay originalEmptyClause noClaimFact :
      Prop) :
    ay_vmdb_unsat_bridge bridgeContract proofReplay originalEmptyClause ->
    ay_vmdb_public_result satFact originalEmptyClause noClaimFact :=
  fun bridge =>
    ay_vmdb_disj_right satFact
      (ay_vmdb_disj originalEmptyClause noClaimFact)
      (ay_vmdb_disj_left originalEmptyClause noClaimFact
        (ay_vmdb_unsat_bridge_original_empty_clause bridgeContract
          proofReplay originalEmptyClause bridge))

theorem ay_vmdb_sat_bridge_requires_same_bridge
    (manifestMembership digestRoot replayTranscript formulaFingerprint
      preprocessReconstruction exitCodeContract modelReplay originalModel :
      Prop) :
    ay_vmdb_sat_bridge
      (ay_vmdb_bridge_contract manifestMembership digestRoot replayTranscript
        formulaFingerprint preprocessReconstruction exitCodeContract)
      modelReplay originalModel ->
    ay_vmdb_bridge_contract manifestMembership digestRoot replayTranscript
      formulaFingerprint preprocessReconstruction exitCodeContract :=
  fun bridge =>
    ay_vmdb_sat_bridge_contract
      (ay_vmdb_bridge_contract manifestMembership digestRoot replayTranscript
        formulaFingerprint preprocessReconstruction exitCodeContract)
      modelReplay originalModel bridge

theorem ay_vmdb_unsat_bridge_requires_same_bridge
    (manifestMembership digestRoot replayTranscript formulaFingerprint
      preprocessReconstruction exitCodeContract proofReplay
      originalEmptyClause : Prop) :
    ay_vmdb_unsat_bridge
      (ay_vmdb_bridge_contract manifestMembership digestRoot replayTranscript
        formulaFingerprint preprocessReconstruction exitCodeContract)
      proofReplay originalEmptyClause ->
    ay_vmdb_bridge_contract manifestMembership digestRoot replayTranscript
      formulaFingerprint preprocessReconstruction exitCodeContract :=
  fun bridge =>
    ay_vmdb_unsat_bridge_contract
      (ay_vmdb_bridge_contract manifestMembership digestRoot replayTranscript
        formulaFingerprint preprocessReconstruction exitCodeContract)
      proofReplay originalEmptyClause bridge

theorem ay_vmdb_stale_digest_root_forces_no_claim
    (satFact unsatFact staleDigest bridgeAudit diagnostic : Prop) :
    staleDigest -> (satFact -> False) -> (unsatFact -> False) ->
    bridgeAudit -> diagnostic ->
    ay_vmdb_failure satFact unsatFact staleDigest bridgeAudit diagnostic :=
  fun reasonProof blockSat blockUnsat auditProof diagnosticProof =>
    ay_vmdb_failure_intro satFact unsatFact staleDigest bridgeAudit
      diagnostic
      (ay_vmdb_blocked_publication_intro satFact unsatFact staleDigest
        reasonProof blockSat blockUnsat)
      (ay_vmdb_recompute_intro staleDigest bridgeAudit diagnostic
        reasonProof auditProof diagnosticProof)

theorem ay_vmdb_missing_manifest_entry_forces_no_claim
    (satFact unsatFact missingManifest bridgeAudit diagnostic : Prop) :
    missingManifest -> (satFact -> False) -> (unsatFact -> False) ->
    bridgeAudit -> diagnostic ->
    ay_vmdb_failure satFact unsatFact missingManifest bridgeAudit
      diagnostic :=
  fun reasonProof blockSat blockUnsat auditProof diagnosticProof =>
    ay_vmdb_failure_intro satFact unsatFact missingManifest bridgeAudit
      diagnostic
      (ay_vmdb_blocked_publication_intro satFact unsatFact missingManifest
        reasonProof blockSat blockUnsat)
      (ay_vmdb_recompute_intro missingManifest bridgeAudit diagnostic
        reasonProof auditProof diagnosticProof)

theorem ay_vmdb_transcript_mismatch_forces_no_claim
    (satFact unsatFact transcriptMismatch bridgeAudit diagnostic : Prop) :
    transcriptMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    bridgeAudit -> diagnostic ->
    ay_vmdb_failure satFact unsatFact transcriptMismatch bridgeAudit
      diagnostic :=
  fun reasonProof blockSat blockUnsat auditProof diagnosticProof =>
    ay_vmdb_failure_intro satFact unsatFact transcriptMismatch bridgeAudit
      diagnostic
      (ay_vmdb_blocked_publication_intro satFact unsatFact
        transcriptMismatch reasonProof blockSat blockUnsat)
      (ay_vmdb_recompute_intro transcriptMismatch bridgeAudit diagnostic
        reasonProof auditProof diagnosticProof)

theorem ay_vmdb_fingerprint_drift_forces_no_claim
    (satFact unsatFact fingerprintDrift bridgeAudit diagnostic : Prop) :
    fingerprintDrift -> (satFact -> False) -> (unsatFact -> False) ->
    bridgeAudit -> diagnostic ->
    ay_vmdb_failure satFact unsatFact fingerprintDrift bridgeAudit
      diagnostic :=
  fun reasonProof blockSat blockUnsat auditProof diagnosticProof =>
    ay_vmdb_failure_intro satFact unsatFact fingerprintDrift bridgeAudit
      diagnostic
      (ay_vmdb_blocked_publication_intro satFact unsatFact
        fingerprintDrift reasonProof blockSat blockUnsat)
      (ay_vmdb_recompute_intro fingerprintDrift bridgeAudit diagnostic
        reasonProof auditProof diagnosticProof)

theorem ay_vmdb_exit_code_mismatch_forces_no_claim
    (satFact unsatFact exitMismatch bridgeAudit diagnostic : Prop) :
    exitMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    bridgeAudit -> diagnostic ->
    ay_vmdb_failure satFact unsatFact exitMismatch bridgeAudit diagnostic :=
  fun reasonProof blockSat blockUnsat auditProof diagnosticProof =>
    ay_vmdb_failure_intro satFact unsatFact exitMismatch bridgeAudit
      diagnostic
      (ay_vmdb_blocked_publication_intro satFact unsatFact exitMismatch
        reasonProof blockSat blockUnsat)
      (ay_vmdb_recompute_intro exitMismatch bridgeAudit diagnostic
        reasonProof auditProof diagnosticProof)

theorem ay_vmdb_failure_cannot_publish_sat
    (satFact unsatFact reason bridgeAudit diagnostic : Prop) :
    ay_vmdb_failure satFact unsatFact reason bridgeAudit diagnostic ->
    satFact -> False :=
  ay_vmdb_failure_blocks_sat satFact unsatFact reason bridgeAudit diagnostic

theorem ay_vmdb_failure_cannot_publish_unsat
    (satFact unsatFact reason bridgeAudit diagnostic : Prop) :
    ay_vmdb_failure satFact unsatFact reason bridgeAudit diagnostic ->
    unsatFact -> False :=
  ay_vmdb_failure_blocks_unsat satFact unsatFact reason bridgeAudit diagnostic
