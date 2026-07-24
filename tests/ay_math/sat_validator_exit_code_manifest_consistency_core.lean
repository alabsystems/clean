-- SAT-COMP validator exit-code/manifest consistency core.
--
-- A public ay result is trusted only when the competition exit code agrees
-- with the public manifest, replayed checker evidence, preprocessing
-- reconstruction, and diagnostic state.  Mismatches route to no-claim or
-- recompute obligations instead of publishing stale SAT/UNSAT facts.

def ay_vecm_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vecm_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vecm_equisat (before after : Prop) : Prop :=
  ay_vecm_conj (before -> after) (after -> before)

def ay_vecm_public_result
    (satFact unsatFact unknownFact noClaimFact : Prop) : Prop :=
  ay_vecm_disj satFact
    (ay_vecm_disj unsatFact
      (ay_vecm_disj unknownFact noClaimFact))

def ay_vecm_manifest_contract
    (exitCode manifestDigest checkerReplay preprocessReconstruction
      diagnosticState : Prop) : Prop :=
  ay_vecm_conj exitCode
    (ay_vecm_conj manifestDigest
      (ay_vecm_conj checkerReplay
        (ay_vecm_conj preprocessReconstruction diagnosticState)))

def ay_vecm_sat_exit
    (manifestContract modelEvidence originalModel : Prop) : Prop :=
  ay_vecm_conj manifestContract
    (ay_vecm_conj modelEvidence originalModel)

def ay_vecm_unsat_exit
    (manifestContract proofEvidence originalEmptyClause : Prop) : Prop :=
  ay_vecm_conj manifestContract
    (ay_vecm_conj proofEvidence originalEmptyClause)

def ay_vecm_unknown_exit
    (exitAgreement manifestDigest diagnosticState noSemanticClaim : Prop) :
    Prop :=
  ay_vecm_conj exitAgreement
    (ay_vecm_conj manifestDigest
      (ay_vecm_conj diagnosticState noSemanticClaim))

def ay_vecm_no_claim_exit
    (reason manifestDigest diagnosticState noSemanticClaim : Prop) : Prop :=
  ay_vecm_conj reason
    (ay_vecm_conj manifestDigest
      (ay_vecm_conj diagnosticState noSemanticClaim))

def ay_vecm_recompute_obligation
    (reason diagnosticState auditTrail : Prop) : Prop :=
  ay_vecm_conj reason (ay_vecm_conj diagnosticState auditTrail)

def ay_vecm_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vecm_conj reason
    (ay_vecm_conj (satFact -> False) (unsatFact -> False))

def ay_vecm_failure
    (satFact unsatFact reason diagnosticState auditTrail : Prop) : Prop :=
  ay_vecm_conj
    (ay_vecm_blocked_publication satFact unsatFact reason)
    (ay_vecm_recompute_obligation reason diagnosticState auditTrail)

def ay_vecm_model (formula assignment : Prop) : Prop :=
  ay_vecm_conj formula assignment

def ay_vecm_unsat (formula : Prop) : Prop :=
  formula -> False

def ay_vecm_preprocess_reconstruction (original solver : Prop) : Prop :=
  ay_vecm_equisat original solver

theorem ay_vecm_conj_intro (left right : Prop) :
    left -> right -> ay_vecm_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vecm_conj_left (left right : Prop) :
    ay_vecm_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vecm_conj_right (left right : Prop) :
    ay_vecm_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vecm_disj_left (left right : Prop) :
    left -> ay_vecm_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vecm_disj_right (left right : Prop) :
    right -> ay_vecm_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vecm_equisat_forward (before after : Prop) :
    ay_vecm_equisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vecm_equisat_backward (before after : Prop) :
    ay_vecm_equisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vecm_model_intro (formula assignment : Prop) :
    formula -> assignment -> ay_vecm_model formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vecm_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vecm_model_formula (formula assignment : Prop) :
    ay_vecm_model formula assignment -> formula :=
  fun model => ay_vecm_conj_left formula assignment model

theorem ay_vecm_model_assignment (formula assignment : Prop) :
    ay_vecm_model formula assignment -> assignment :=
  fun model => ay_vecm_conj_right formula assignment model

theorem ay_vecm_manifest_contract_intro
    (exitCode manifestDigest checkerReplay preprocessReconstruction
      diagnosticState : Prop) :
    exitCode -> manifestDigest -> checkerReplay ->
    preprocessReconstruction -> diagnosticState ->
    ay_vecm_manifest_contract exitCode manifestDigest checkerReplay
      preprocessReconstruction diagnosticState :=
  fun exitProof digestProof replayProof reconstructionProof diagnosticProof =>
    ay_vecm_conj_intro exitCode
      (ay_vecm_conj manifestDigest
        (ay_vecm_conj checkerReplay
          (ay_vecm_conj preprocessReconstruction diagnosticState)))
      exitProof
      (ay_vecm_conj_intro manifestDigest
        (ay_vecm_conj checkerReplay
          (ay_vecm_conj preprocessReconstruction diagnosticState))
        digestProof
        (ay_vecm_conj_intro checkerReplay
          (ay_vecm_conj preprocessReconstruction diagnosticState)
          replayProof
          (ay_vecm_conj_intro preprocessReconstruction diagnosticState
            reconstructionProof diagnosticProof)))

theorem ay_vecm_manifest_contract_exit
    (exitCode manifestDigest checkerReplay preprocessReconstruction
      diagnosticState : Prop) :
    ay_vecm_manifest_contract exitCode manifestDigest checkerReplay
      preprocessReconstruction diagnosticState ->
    exitCode :=
  fun contract =>
    ay_vecm_conj_left exitCode
      (ay_vecm_conj manifestDigest
        (ay_vecm_conj checkerReplay
          (ay_vecm_conj preprocessReconstruction diagnosticState)))
      contract

theorem ay_vecm_manifest_contract_digest
    (exitCode manifestDigest checkerReplay preprocessReconstruction
      diagnosticState : Prop) :
    ay_vecm_manifest_contract exitCode manifestDigest checkerReplay
      preprocessReconstruction diagnosticState ->
    manifestDigest :=
  fun contract =>
    ay_vecm_conj_right exitCode
      (ay_vecm_conj manifestDigest
        (ay_vecm_conj checkerReplay
          (ay_vecm_conj preprocessReconstruction diagnosticState)))
      contract manifestDigest
      (fun digestProof _tail => digestProof)

theorem ay_vecm_manifest_contract_replay
    (exitCode manifestDigest checkerReplay preprocessReconstruction
      diagnosticState : Prop) :
    ay_vecm_manifest_contract exitCode manifestDigest checkerReplay
      preprocessReconstruction diagnosticState ->
    checkerReplay :=
  fun contract =>
    ay_vecm_conj_right exitCode
      (ay_vecm_conj manifestDigest
        (ay_vecm_conj checkerReplay
          (ay_vecm_conj preprocessReconstruction diagnosticState)))
      contract checkerReplay
      (fun _digestProof tail =>
        tail checkerReplay (fun replayProof _tail2 => replayProof))

theorem ay_vecm_manifest_contract_reconstruction
    (exitCode manifestDigest checkerReplay preprocessReconstruction
      diagnosticState : Prop) :
    ay_vecm_manifest_contract exitCode manifestDigest checkerReplay
      preprocessReconstruction diagnosticState ->
    preprocessReconstruction :=
  fun contract =>
    ay_vecm_conj_right exitCode
      (ay_vecm_conj manifestDigest
        (ay_vecm_conj checkerReplay
          (ay_vecm_conj preprocessReconstruction diagnosticState)))
      contract preprocessReconstruction
      (fun _digestProof tail =>
        tail preprocessReconstruction
          (fun _replayProof tail2 =>
            tail2 preprocessReconstruction
              (fun reconstructionProof _diagnosticProof =>
                reconstructionProof)))

theorem ay_vecm_manifest_contract_diagnostic
    (exitCode manifestDigest checkerReplay preprocessReconstruction
      diagnosticState : Prop) :
    ay_vecm_manifest_contract exitCode manifestDigest checkerReplay
      preprocessReconstruction diagnosticState ->
    diagnosticState :=
  fun contract =>
    ay_vecm_conj_right exitCode
      (ay_vecm_conj manifestDigest
        (ay_vecm_conj checkerReplay
          (ay_vecm_conj preprocessReconstruction diagnosticState)))
      contract diagnosticState
      (fun _digestProof tail =>
        tail diagnosticState
          (fun _replayProof tail2 =>
            tail2 diagnosticState
              (fun _reconstructionProof diagnosticProof =>
                diagnosticProof)))

theorem ay_vecm_sat_exit_intro
    (manifestContract modelEvidence originalModel : Prop) :
    manifestContract -> modelEvidence -> originalModel ->
    ay_vecm_sat_exit manifestContract modelEvidence originalModel :=
  fun contractProof modelProof originalProof =>
    ay_vecm_conj_intro manifestContract
      (ay_vecm_conj modelEvidence originalModel)
      contractProof
      (ay_vecm_conj_intro modelEvidence originalModel modelProof
        originalProof)

theorem ay_vecm_sat_exit_contract
    (manifestContract modelEvidence originalModel : Prop) :
    ay_vecm_sat_exit manifestContract modelEvidence originalModel ->
    manifestContract :=
  fun satExit =>
    ay_vecm_conj_left manifestContract
      (ay_vecm_conj modelEvidence originalModel) satExit

theorem ay_vecm_sat_exit_model_evidence
    (manifestContract modelEvidence originalModel : Prop) :
    ay_vecm_sat_exit manifestContract modelEvidence originalModel ->
    modelEvidence :=
  fun satExit =>
    ay_vecm_conj_right manifestContract
      (ay_vecm_conj modelEvidence originalModel)
      satExit modelEvidence
      (fun modelProof _originalProof => modelProof)

theorem ay_vecm_sat_exit_original_model
    (manifestContract modelEvidence originalModel : Prop) :
    ay_vecm_sat_exit manifestContract modelEvidence originalModel ->
    originalModel :=
  fun satExit =>
    ay_vecm_conj_right manifestContract
      (ay_vecm_conj modelEvidence originalModel)
      satExit originalModel
      (fun _modelProof originalProof => originalProof)

theorem ay_vecm_unsat_exit_intro
    (manifestContract proofEvidence originalEmptyClause : Prop) :
    manifestContract -> proofEvidence -> originalEmptyClause ->
    ay_vecm_unsat_exit manifestContract proofEvidence
      originalEmptyClause :=
  fun contractProof proofEvidenceProof emptyClauseProof =>
    ay_vecm_conj_intro manifestContract
      (ay_vecm_conj proofEvidence originalEmptyClause)
      contractProof
      (ay_vecm_conj_intro proofEvidence originalEmptyClause
        proofEvidenceProof emptyClauseProof)

theorem ay_vecm_unsat_exit_contract
    (manifestContract proofEvidence originalEmptyClause : Prop) :
    ay_vecm_unsat_exit manifestContract proofEvidence
      originalEmptyClause ->
    manifestContract :=
  fun unsatExit =>
    ay_vecm_conj_left manifestContract
      (ay_vecm_conj proofEvidence originalEmptyClause) unsatExit

theorem ay_vecm_unsat_exit_proof_evidence
    (manifestContract proofEvidence originalEmptyClause : Prop) :
    ay_vecm_unsat_exit manifestContract proofEvidence
      originalEmptyClause ->
    proofEvidence :=
  fun unsatExit =>
    ay_vecm_conj_right manifestContract
      (ay_vecm_conj proofEvidence originalEmptyClause)
      unsatExit proofEvidence
      (fun proofEvidenceProof _emptyClauseProof => proofEvidenceProof)

theorem ay_vecm_unsat_exit_original_empty_clause
    (manifestContract proofEvidence originalEmptyClause : Prop) :
    ay_vecm_unsat_exit manifestContract proofEvidence
      originalEmptyClause ->
    originalEmptyClause :=
  fun unsatExit =>
    ay_vecm_conj_right manifestContract
      (ay_vecm_conj proofEvidence originalEmptyClause)
      unsatExit originalEmptyClause
      (fun _proofEvidenceProof emptyClauseProof => emptyClauseProof)

theorem ay_vecm_unknown_exit_intro
    (exitAgreement manifestDigest diagnosticState noSemanticClaim : Prop) :
    exitAgreement -> manifestDigest -> diagnosticState ->
    noSemanticClaim ->
    ay_vecm_unknown_exit exitAgreement manifestDigest diagnosticState
      noSemanticClaim :=
  fun exitProof digestProof diagnosticProof noClaimProof =>
    ay_vecm_conj_intro exitAgreement
      (ay_vecm_conj manifestDigest
        (ay_vecm_conj diagnosticState noSemanticClaim))
      exitProof
      (ay_vecm_conj_intro manifestDigest
        (ay_vecm_conj diagnosticState noSemanticClaim)
        digestProof
        (ay_vecm_conj_intro diagnosticState noSemanticClaim
          diagnosticProof noClaimProof))

theorem ay_vecm_unknown_exit_no_semantic_claim
    (exitAgreement manifestDigest diagnosticState noSemanticClaim : Prop) :
    ay_vecm_unknown_exit exitAgreement manifestDigest diagnosticState
      noSemanticClaim ->
    noSemanticClaim :=
  fun unknownExit =>
    ay_vecm_conj_right exitAgreement
      (ay_vecm_conj manifestDigest
        (ay_vecm_conj diagnosticState noSemanticClaim))
      unknownExit noSemanticClaim
      (fun _digestProof tail =>
        tail noSemanticClaim
          (fun _diagnosticProof noClaimProof => noClaimProof))

theorem ay_vecm_no_claim_exit_intro
    (reason manifestDigest diagnosticState noSemanticClaim : Prop) :
    reason -> manifestDigest -> diagnosticState -> noSemanticClaim ->
    ay_vecm_no_claim_exit reason manifestDigest diagnosticState
      noSemanticClaim :=
  fun reasonProof digestProof diagnosticProof noClaimProof =>
    ay_vecm_conj_intro reason
      (ay_vecm_conj manifestDigest
        (ay_vecm_conj diagnosticState noSemanticClaim))
      reasonProof
      (ay_vecm_conj_intro manifestDigest
        (ay_vecm_conj diagnosticState noSemanticClaim)
        digestProof
        (ay_vecm_conj_intro diagnosticState noSemanticClaim
          diagnosticProof noClaimProof))

theorem ay_vecm_no_claim_exit_no_semantic_claim
    (reason manifestDigest diagnosticState noSemanticClaim : Prop) :
    ay_vecm_no_claim_exit reason manifestDigest diagnosticState
      noSemanticClaim ->
    noSemanticClaim :=
  fun noClaimExit =>
    ay_vecm_conj_right reason
      (ay_vecm_conj manifestDigest
        (ay_vecm_conj diagnosticState noSemanticClaim))
      noClaimExit noSemanticClaim
      (fun _digestProof tail =>
        tail noSemanticClaim
          (fun _diagnosticProof noClaimProof => noClaimProof))

theorem ay_vecm_recompute_obligation_intro
    (reason diagnosticState auditTrail : Prop) :
    reason -> diagnosticState -> auditTrail ->
    ay_vecm_recompute_obligation reason diagnosticState auditTrail :=
  fun reasonProof diagnosticProof auditProof =>
    ay_vecm_conj_intro reason
      (ay_vecm_conj diagnosticState auditTrail)
      reasonProof
      (ay_vecm_conj_intro diagnosticState auditTrail diagnosticProof
        auditProof)

theorem ay_vecm_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vecm_blocked_publication satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vecm_conj_intro reason
      (ay_vecm_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vecm_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vecm_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vecm_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vecm_conj_right reason
      (ay_vecm_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vecm_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vecm_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vecm_conj_right reason
      (ay_vecm_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vecm_failure_intro
    (satFact unsatFact reason diagnosticState auditTrail : Prop) :
    ay_vecm_blocked_publication satFact unsatFact reason ->
    ay_vecm_recompute_obligation reason diagnosticState auditTrail ->
    ay_vecm_failure satFact unsatFact reason diagnosticState auditTrail :=
  fun blocked recompute =>
    ay_vecm_conj_intro
      (ay_vecm_blocked_publication satFact unsatFact reason)
      (ay_vecm_recompute_obligation reason diagnosticState auditTrail)
      blocked recompute

theorem ay_vecm_failure_blocks_sat
    (satFact unsatFact reason diagnosticState auditTrail : Prop) :
    ay_vecm_failure satFact unsatFact reason diagnosticState auditTrail ->
    satFact -> False :=
  fun failure =>
    ay_vecm_blocked_publication_no_sat satFact unsatFact reason
      (ay_vecm_conj_left
        (ay_vecm_blocked_publication satFact unsatFact reason)
        (ay_vecm_recompute_obligation reason diagnosticState auditTrail)
        failure)

theorem ay_vecm_failure_blocks_unsat
    (satFact unsatFact reason diagnosticState auditTrail : Prop) :
    ay_vecm_failure satFact unsatFact reason diagnosticState auditTrail ->
    unsatFact -> False :=
  fun failure =>
    ay_vecm_blocked_publication_no_unsat satFact unsatFact reason
      (ay_vecm_conj_left
        (ay_vecm_blocked_publication satFact unsatFact reason)
        (ay_vecm_recompute_obligation reason diagnosticState auditTrail)
        failure)

theorem ay_vecm_failure_recompute
    (satFact unsatFact reason diagnosticState auditTrail : Prop) :
    ay_vecm_failure satFact unsatFact reason diagnosticState auditTrail ->
    ay_vecm_recompute_obligation reason diagnosticState auditTrail :=
  fun failure =>
    ay_vecm_conj_right
      (ay_vecm_blocked_publication satFact unsatFact reason)
      (ay_vecm_recompute_obligation reason diagnosticState auditTrail)
      failure

theorem ay_vecm_preprocess_model_reconstruct
    (original solver assignment : Prop) :
    ay_vecm_preprocess_reconstruction original solver ->
    ay_vecm_model solver assignment ->
    ay_vecm_model original assignment :=
  fun reconstruction solverModel =>
    ay_vecm_model_intro original assignment
      (ay_vecm_equisat_backward original solver reconstruction
        (ay_vecm_model_formula solver assignment solverModel))
      (ay_vecm_model_assignment solver assignment solverModel)

theorem ay_vecm_preprocess_unsat_reconstruct
    (original solver : Prop) :
    ay_vecm_preprocess_reconstruction original solver ->
    ay_vecm_unsat solver ->
    ay_vecm_unsat original :=
  fun reconstruction solverUnsat originalProof =>
    solverUnsat
      (ay_vecm_equisat_forward original solver reconstruction originalProof)

theorem ay_vecm_sat_exit_requires_original_evidence
    (manifestContract modelEvidence originalModel : Prop) :
    ay_vecm_sat_exit manifestContract modelEvidence originalModel ->
    ay_vecm_conj manifestContract
      (ay_vecm_conj modelEvidence originalModel) :=
  fun satExit => satExit

theorem ay_vecm_unsat_exit_requires_original_evidence
    (manifestContract proofEvidence originalEmptyClause : Prop) :
    ay_vecm_unsat_exit manifestContract proofEvidence
      originalEmptyClause ->
    ay_vecm_conj manifestContract
      (ay_vecm_conj proofEvidence originalEmptyClause) :=
  fun unsatExit => unsatExit

theorem ay_vecm_sat_public_result
    (manifestContract modelEvidence originalModel unsatFact unknownFact
      noClaimFact : Prop) :
    ay_vecm_sat_exit manifestContract modelEvidence originalModel ->
    ay_vecm_public_result originalModel unsatFact unknownFact noClaimFact :=
  fun satExit =>
    ay_vecm_disj_left originalModel
      (ay_vecm_disj unsatFact
        (ay_vecm_disj unknownFact noClaimFact))
      (ay_vecm_sat_exit_original_model manifestContract modelEvidence
        originalModel satExit)

theorem ay_vecm_unsat_public_result
    (satFact manifestContract proofEvidence originalEmptyClause unknownFact
      noClaimFact : Prop) :
    ay_vecm_unsat_exit manifestContract proofEvidence
      originalEmptyClause ->
    ay_vecm_public_result satFact originalEmptyClause unknownFact
      noClaimFact :=
  fun unsatExit =>
    ay_vecm_disj_right satFact
      (ay_vecm_disj originalEmptyClause
        (ay_vecm_disj unknownFact noClaimFact))
      (ay_vecm_disj_left originalEmptyClause
        (ay_vecm_disj unknownFact noClaimFact)
        (ay_vecm_unsat_exit_original_empty_clause manifestContract
          proofEvidence originalEmptyClause unsatExit))

theorem ay_vecm_unknown_public_result
    (satFact unsatFact exitAgreement manifestDigest diagnosticState
      noSemanticClaim : Prop) :
    ay_vecm_unknown_exit exitAgreement manifestDigest diagnosticState
      noSemanticClaim ->
    ay_vecm_public_result satFact unsatFact noSemanticClaim noSemanticClaim :=
  fun unknownExit =>
    ay_vecm_disj_right satFact
      (ay_vecm_disj unsatFact
        (ay_vecm_disj noSemanticClaim noSemanticClaim))
      (ay_vecm_disj_right unsatFact
        (ay_vecm_disj noSemanticClaim noSemanticClaim)
        (ay_vecm_disj_left noSemanticClaim noSemanticClaim
          (ay_vecm_unknown_exit_no_semantic_claim exitAgreement
            manifestDigest diagnosticState noSemanticClaim unknownExit)))

theorem ay_vecm_no_claim_public_result
    (satFact unsatFact unknownFact reason manifestDigest diagnosticState
      noSemanticClaim : Prop) :
    ay_vecm_no_claim_exit reason manifestDigest diagnosticState
      noSemanticClaim ->
    ay_vecm_public_result satFact unsatFact unknownFact noSemanticClaim :=
  fun noClaimExit =>
    ay_vecm_disj_right satFact
      (ay_vecm_disj unsatFact
        (ay_vecm_disj unknownFact noSemanticClaim))
      (ay_vecm_disj_right unsatFact
        (ay_vecm_disj unknownFact noSemanticClaim)
        (ay_vecm_disj_right unknownFact noSemanticClaim
          (ay_vecm_no_claim_exit_no_semantic_claim reason manifestDigest
            diagnosticState noSemanticClaim noClaimExit)))

theorem ay_vecm_mismatched_exit_code_forces_recompute
    (satFact unsatFact exitMismatch diagnosticState auditTrail : Prop) :
    exitMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    diagnosticState -> auditTrail ->
    ay_vecm_failure satFact unsatFact exitMismatch diagnosticState
      auditTrail :=
  fun reasonProof blockSat blockUnsat diagnosticProof auditProof =>
    ay_vecm_failure_intro satFact unsatFact exitMismatch diagnosticState
      auditTrail
      (ay_vecm_blocked_publication_intro satFact unsatFact exitMismatch
        reasonProof blockSat blockUnsat)
      (ay_vecm_recompute_obligation_intro exitMismatch diagnosticState
        auditTrail reasonProof diagnosticProof auditProof)

theorem ay_vecm_stale_manifest_digest_forces_recompute
    (satFact unsatFact staleDigest diagnosticState auditTrail : Prop) :
    staleDigest -> (satFact -> False) -> (unsatFact -> False) ->
    diagnosticState -> auditTrail ->
    ay_vecm_failure satFact unsatFact staleDigest diagnosticState
      auditTrail :=
  fun reasonProof blockSat blockUnsat diagnosticProof auditProof =>
    ay_vecm_failure_intro satFact unsatFact staleDigest diagnosticState
      auditTrail
      (ay_vecm_blocked_publication_intro satFact unsatFact staleDigest
        reasonProof blockSat blockUnsat)
      (ay_vecm_recompute_obligation_intro staleDigest diagnosticState
        auditTrail reasonProof diagnosticProof auditProof)

theorem ay_vecm_missing_checker_replay_forces_recompute
    (satFact unsatFact missingReplay diagnosticState auditTrail : Prop) :
    missingReplay -> (satFact -> False) -> (unsatFact -> False) ->
    diagnosticState -> auditTrail ->
    ay_vecm_failure satFact unsatFact missingReplay diagnosticState
      auditTrail :=
  fun reasonProof blockSat blockUnsat diagnosticProof auditProof =>
    ay_vecm_failure_intro satFact unsatFact missingReplay diagnosticState
      auditTrail
      (ay_vecm_blocked_publication_intro satFact unsatFact missingReplay
        reasonProof blockSat blockUnsat)
      (ay_vecm_recompute_obligation_intro missingReplay diagnosticState
        auditTrail reasonProof diagnosticProof auditProof)

theorem ay_vecm_contradictory_diagnostics_force_recompute
    (satFact unsatFact contradictoryDiagnostics diagnosticState
      auditTrail : Prop) :
    contradictoryDiagnostics -> (satFact -> False) ->
    (unsatFact -> False) -> diagnosticState -> auditTrail ->
    ay_vecm_failure satFact unsatFact contradictoryDiagnostics
      diagnosticState auditTrail :=
  fun reasonProof blockSat blockUnsat diagnosticProof auditProof =>
    ay_vecm_failure_intro satFact unsatFact contradictoryDiagnostics
      diagnosticState auditTrail
      (ay_vecm_blocked_publication_intro satFact unsatFact
        contradictoryDiagnostics reasonProof blockSat blockUnsat)
      (ay_vecm_recompute_obligation_intro contradictoryDiagnostics
        diagnosticState auditTrail reasonProof diagnosticProof auditProof)

theorem ay_vecm_failure_cannot_publish_sat
    (satFact unsatFact reason diagnosticState auditTrail : Prop) :
    ay_vecm_failure satFact unsatFact reason diagnosticState auditTrail ->
    satFact -> False :=
  ay_vecm_failure_blocks_sat satFact unsatFact reason diagnosticState
    auditTrail

theorem ay_vecm_failure_cannot_publish_unsat
    (satFact unsatFact reason diagnosticState auditTrail : Prop) :
    ay_vecm_failure satFact unsatFact reason diagnosticState auditTrail ->
    unsatFact -> False :=
  ay_vecm_failure_blocks_unsat satFact unsatFact reason diagnosticState
    auditTrail
