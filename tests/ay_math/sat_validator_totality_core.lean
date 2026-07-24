-- SAT-COMP validator totality core.
--
-- This self-contained package models a total ay validator classification:
-- every parser/checker/archive state is accepted SAT, accepted UNSAT, or an
-- explicit no-claim failure.  The failure branch never yields semantic
-- SAT/UNSAT evidence; accepted branches retain their soundness obligations.

def AyVTCConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVTCDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVTCEquisat (before after : Prop) : Prop :=
  AyVTCConj (before -> after) (after -> before)

def AyVTCOutcome (sat unsat : Prop) : Prop :=
  AyVTCDisj sat unsat

def AyVTCClassified (satFact unsatFact noClaim : Prop) : Prop :=
  AyVTCDisj satFact (AyVTCDisj unsatFact noClaim)

def AyVTCFailure
    (parseFailure missingArtifact checkerReject archiveBad unknown : Prop) :
    Prop :=
  AyVTCDisj parseFailure
    (AyVTCDisj missingArtifact
      (AyVTCDisj checkerReject (AyVTCDisj archiveBad unknown)))

def AyVTCNoClaim (reason archiveState : Prop) : Prop :=
  AyVTCConj reason archiveState

def AyVTCModel (formula assignment : Prop) : Prop :=
  AyVTCConj formula assignment

def AyVTCUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVTCVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVTCModel original visibleAssignment

def AyVTCSatChecker (branch visibleSat : Prop) : Prop :=
  branch -> visibleSat

def AyVTCUnsatChecker (branch publicUnsat : Prop) : Prop :=
  branch -> publicUnsat

def AyVTCPreprocessArtifact (original solver : Prop) : Prop :=
  AyVTCEquisat original solver

def AyVTCReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

def AyVTCCompressed (payload : Prop) : Prop :=
  payload

def AyVTCIndexed (index payload : Prop) : Prop :=
  AyVTCConj index payload

def AyVTCTotalState (acceptedSat acceptedUnsat failure : Prop) : Prop :=
  AyVTCDisj acceptedSat (AyVTCDisj acceptedUnsat failure)

theorem ay_vtc_conj_intro (left right : Prop) :
    left -> right -> AyVTCConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vtc_conj_left (left right : Prop) :
    AyVTCConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vtc_conj_right (left right : Prop) :
    AyVTCConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vtc_disj_left (left right : Prop) :
    left -> AyVTCDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vtc_disj_right (left right : Prop) :
    right -> AyVTCDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vtc_equisat_forward (before after : Prop) :
    AyVTCEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vtc_equisat_backward (before after : Prop) :
    AyVTCEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vtc_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVTCModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vtc_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vtc_model_formula (formula assignment : Prop) :
    AyVTCModel formula assignment -> formula :=
  fun model => ay_vtc_conj_left formula assignment model

theorem ay_vtc_model_assignment (formula assignment : Prop) :
    AyVTCModel formula assignment -> assignment :=
  fun model => ay_vtc_conj_right formula assignment model

theorem ay_vtc_compressed_expand (payload : Prop) :
    AyVTCCompressed payload -> payload :=
  fun compressed => compressed

theorem ay_vtc_compressed_pack (payload : Prop) :
    payload -> AyVTCCompressed payload :=
  fun payloadProof => payloadProof

theorem ay_vtc_indexed_intro (index payload : Prop) :
    index -> payload -> AyVTCIndexed index payload :=
  fun indexProof payloadProof =>
    ay_vtc_conj_intro index payload indexProof payloadProof

theorem ay_vtc_indexed_index (index payload : Prop) :
    AyVTCIndexed index payload -> index :=
  fun indexed => ay_vtc_conj_left index payload indexed

theorem ay_vtc_indexed_payload (index payload : Prop) :
    AyVTCIndexed index payload -> payload :=
  fun indexed => ay_vtc_conj_right index payload indexed

theorem ay_vtc_indexed_compressed_lookup (index payload : Prop) :
    AyVTCIndexed index (AyVTCCompressed payload) ->
    index ->
    payload :=
  fun indexed _indexProof =>
    ay_vtc_compressed_expand payload
      (ay_vtc_indexed_payload index (AyVTCCompressed payload) indexed)

theorem ay_vtc_no_claim_intro (reason archiveState : Prop) :
    reason -> archiveState -> AyVTCNoClaim reason archiveState :=
  ay_vtc_conj_intro reason archiveState

theorem ay_vtc_no_claim_reason (reason archiveState : Prop) :
    AyVTCNoClaim reason archiveState -> reason :=
  ay_vtc_conj_left reason archiveState

theorem ay_vtc_no_claim_archive (reason archiveState : Prop) :
    AyVTCNoClaim reason archiveState -> archiveState :=
  ay_vtc_conj_right reason archiveState

theorem ay_vtc_parse_failure_no_claim
    (parseFailure archiveState : Prop) :
    parseFailure -> archiveState ->
    AyVTCNoClaim parseFailure archiveState :=
  ay_vtc_no_claim_intro parseFailure archiveState

theorem ay_vtc_missing_artifact_no_claim
    (missingArtifact archiveState : Prop) :
    missingArtifact -> archiveState ->
    AyVTCNoClaim missingArtifact archiveState :=
  ay_vtc_no_claim_intro missingArtifact archiveState

theorem ay_vtc_checker_reject_no_claim
    (checkerReject archiveState : Prop) :
    checkerReject -> archiveState ->
    AyVTCNoClaim checkerReject archiveState :=
  ay_vtc_no_claim_intro checkerReject archiveState

theorem ay_vtc_archive_bad_no_claim
    (archiveBad archiveState : Prop) :
    archiveBad -> archiveState -> AyVTCNoClaim archiveBad archiveState :=
  ay_vtc_no_claim_intro archiveBad archiveState

theorem ay_vtc_unknown_no_claim
    (unknown archiveState : Prop) :
    unknown -> archiveState -> AyVTCNoClaim unknown archiveState :=
  ay_vtc_no_claim_intro unknown archiveState

theorem ay_vtc_failure_total_no_claim
    (parseFailure missingArtifact checkerReject archiveBad unknown
      archiveState : Prop) :
    (parseFailure -> archiveState) ->
    (missingArtifact -> archiveState) ->
    (checkerReject -> archiveState) ->
    (archiveBad -> archiveState) ->
    (unknown -> archiveState) ->
    AyVTCFailure parseFailure missingArtifact checkerReject archiveBad
      unknown ->
    AyVTCDisj
      (AyVTCNoClaim parseFailure archiveState)
      (AyVTCDisj
        (AyVTCNoClaim missingArtifact archiveState)
        (AyVTCDisj
          (AyVTCNoClaim checkerReject archiveState)
          (AyVTCDisj
            (AyVTCNoClaim archiveBad archiveState)
            (AyVTCNoClaim unknown archiveState)))) :=
  fun parseArchive missingArchive rejectArchive badArchive unknownArchive
      failure result onParse onRest =>
    failure result
      (fun parseProof =>
        onParse
          (ay_vtc_parse_failure_no_claim parseFailure archiveState
            parseProof (parseArchive parseProof)))
      (fun rest1 =>
        rest1 result
          (fun missingProof =>
            onRest
              (ay_vtc_disj_left
                (AyVTCNoClaim missingArtifact archiveState)
                (AyVTCDisj
                  (AyVTCNoClaim checkerReject archiveState)
                  (AyVTCDisj
                    (AyVTCNoClaim archiveBad archiveState)
                    (AyVTCNoClaim unknown archiveState)))
                (ay_vtc_missing_artifact_no_claim missingArtifact archiveState
                  missingProof (missingArchive missingProof))))
          (fun rest2 =>
            rest2 result
              (fun rejectProof =>
                onRest
                  (ay_vtc_disj_right
                    (AyVTCNoClaim missingArtifact archiveState)
                    (AyVTCDisj
                      (AyVTCNoClaim checkerReject archiveState)
                      (AyVTCDisj
                        (AyVTCNoClaim archiveBad archiveState)
                        (AyVTCNoClaim unknown archiveState)))
                    (ay_vtc_disj_left
                      (AyVTCNoClaim checkerReject archiveState)
                      (AyVTCDisj
                        (AyVTCNoClaim archiveBad archiveState)
                        (AyVTCNoClaim unknown archiveState))
                      (ay_vtc_checker_reject_no_claim checkerReject
                        archiveState rejectProof
                        (rejectArchive rejectProof)))))
              (fun rest3 =>
                rest3 result
                  (fun badProof =>
                    onRest
                      (ay_vtc_disj_right
                        (AyVTCNoClaim missingArtifact archiveState)
                        (AyVTCDisj
                          (AyVTCNoClaim checkerReject archiveState)
                          (AyVTCDisj
                            (AyVTCNoClaim archiveBad archiveState)
                            (AyVTCNoClaim unknown archiveState)))
                        (ay_vtc_disj_right
                          (AyVTCNoClaim checkerReject archiveState)
                          (AyVTCDisj
                            (AyVTCNoClaim archiveBad archiveState)
                            (AyVTCNoClaim unknown archiveState))
                          (ay_vtc_disj_left
                            (AyVTCNoClaim archiveBad archiveState)
                            (AyVTCNoClaim unknown archiveState)
                            (ay_vtc_archive_bad_no_claim archiveBad
                              archiveState badProof
                              (badArchive badProof))))))
                  (fun unknownProof =>
                    onRest
                      (ay_vtc_disj_right
                        (AyVTCNoClaim missingArtifact archiveState)
                        (AyVTCDisj
                          (AyVTCNoClaim checkerReject archiveState)
                          (AyVTCDisj
                            (AyVTCNoClaim archiveBad archiveState)
                            (AyVTCNoClaim unknown archiveState)))
                        (ay_vtc_disj_right
                          (AyVTCNoClaim checkerReject archiveState)
                          (AyVTCDisj
                            (AyVTCNoClaim archiveBad archiveState)
                            (AyVTCNoClaim unknown archiveState))
                          (ay_vtc_disj_right
                            (AyVTCNoClaim archiveBad archiveState)
                            (AyVTCNoClaim unknown archiveState)
                            (ay_vtc_unknown_no_claim unknown archiveState
                              unknownProof
                              (unknownArchive unknownProof)))))))))

theorem ay_vtc_outcome_map
    (beforeSat afterSat beforeUnsat afterUnsat : Prop) :
    (beforeSat -> afterSat) ->
    (beforeUnsat -> afterUnsat) ->
    AyVTCOutcome beforeSat beforeUnsat ->
    AyVTCOutcome afterSat afterUnsat :=
  fun satMap unsatMap outcome result onSat onUnsat =>
    outcome result
      (fun satProof => onSat (satMap satProof))
      (fun unsatProof => onUnsat (unsatMap unsatProof))

theorem ay_vtc_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVTCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVTCModel solver internalAssignment ->
    AyVTCVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vtc_model_intro original visibleAssignment
      (ay_vtc_equisat_backward original solver preprocess
        (ay_vtc_model_formula solver internalAssignment model))
      (decode (ay_vtc_model_assignment solver internalAssignment model))

theorem ay_vtc_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVTCPreprocessArtifact original solver ->
    AyVTCUnsat solver ->
    AyVTCUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vtc_equisat_forward original solver preprocess originalProof)

theorem ay_vtc_replay_unsat_solver
    (solver stream finalClause : Prop) :
    AyVTCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVTCUnsat solver :=
  fun replay closeFinal streamProof solverProof =>
    closeFinal (replay streamProof solverProof)

theorem ay_vtc_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVTCPreprocessArtifact original solver ->
    AyVTCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVTCUnsat original :=
  fun preprocess replay closeFinal streamProof =>
    ay_vtc_preprocess_unsat_reconstruct original solver preprocess
      (ay_vtc_replay_unsat_solver solver stream finalClause replay
        closeFinal streamProof)

theorem ay_vtc_sat_checker_sound
    (original solver internalAssignment visibleAssignment satBranch : Prop) :
    AyVTCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVTCModel solver internalAssignment) ->
    AyVTCSatChecker satBranch
      (AyVTCVisibleSAT original visibleAssignment) :=
  fun preprocess decode accept branchProof =>
    ay_vtc_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode (accept branchProof)

theorem ay_vtc_unsat_checker_sound
    (original solver stream finalClause unsatBranch : Prop) :
    AyVTCPreprocessArtifact original solver ->
    AyVTCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVTCUnsatChecker unsatBranch (AyVTCUnsat original) :=
  fun preprocess replay closeFinal accept branchProof =>
    ay_vtc_replay_unsat_public original solver stream finalClause
      preprocess replay closeFinal (accept branchProof)

theorem ay_vtc_accepted_outcome_sound
    (satBranch unsatBranch publicSat publicUnsat : Prop) :
    AyVTCSatChecker satBranch publicSat ->
    AyVTCUnsatChecker unsatBranch publicUnsat ->
    AyVTCOutcome satBranch unsatBranch ->
    AyVTCOutcome publicSat publicUnsat :=
  fun satChecker unsatChecker =>
    ay_vtc_outcome_map satBranch publicSat unsatBranch publicUnsat
      satChecker unsatChecker

theorem ay_vtc_indexed_accepted_outcome_sound
    (index satBranch unsatBranch publicSat publicUnsat : Prop) :
    AyVTCSatChecker satBranch publicSat ->
    AyVTCUnsatChecker unsatBranch publicUnsat ->
    AyVTCIndexed index
      (AyVTCCompressed (AyVTCOutcome satBranch unsatBranch)) ->
    index ->
    AyVTCOutcome publicSat publicUnsat :=
  fun satChecker unsatChecker indexed indexProof =>
    ay_vtc_accepted_outcome_sound satBranch unsatBranch publicSat
      publicUnsat satChecker unsatChecker
      (ay_vtc_indexed_compressed_lookup index
        (AyVTCOutcome satBranch unsatBranch) indexed indexProof)

theorem ay_vtc_total_dispatch
    (acceptedSat acceptedUnsat failure publicSat publicUnsat noClaim : Prop) :
    (acceptedSat -> publicSat) ->
    (acceptedUnsat -> publicUnsat) ->
    (failure -> noClaim) ->
    AyVTCTotalState acceptedSat acceptedUnsat failure ->
    AyVTCClassified publicSat publicUnsat noClaim :=
  fun satSound unsatSound failureNoClaim total result onSat onRest =>
    total result
      (fun satProof => onSat (satSound satProof))
      (fun rest =>
        rest result
          (fun unsatProof =>
            onRest
              (ay_vtc_disj_left publicUnsat noClaim
                (unsatSound unsatProof)))
          (fun failureProof =>
            onRest
              (ay_vtc_disj_right publicUnsat noClaim
                (failureNoClaim failureProof))))

theorem ay_vtc_total_dispatch_indexed
    (index satBranch unsatBranch failure publicSat publicUnsat noClaim : Prop) :
    AyVTCSatChecker satBranch publicSat ->
    AyVTCUnsatChecker unsatBranch publicUnsat ->
    (failure -> noClaim) ->
    AyVTCIndexed index
      (AyVTCCompressed (AyVTCOutcome satBranch unsatBranch)) ->
    index ->
    AyVTCTotalState satBranch unsatBranch failure ->
    AyVTCClassified publicSat publicUnsat noClaim :=
  fun satChecker unsatChecker failureNoClaim _indexed _indexProof total =>
    ay_vtc_total_dispatch satBranch unsatBranch failure publicSat publicUnsat
      noClaim satChecker unsatChecker failureNoClaim total

theorem ay_vtc_no_silent_semantic_claim
    (satFact unsatFact noClaim : Prop) :
    noClaim ->
    AyVTCClassified satFact unsatFact noClaim :=
  fun noClaimProof =>
    ay_vtc_disj_right satFact (AyVTCDisj unsatFact noClaim)
      (ay_vtc_disj_right unsatFact noClaim noClaimProof)

theorem ay_vtc_accepted_sat_branch_sound
    (original solver internalAssignment visibleAssignment satBranch : Prop) :
    AyVTCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVTCModel solver internalAssignment) ->
    satBranch ->
    AyVTCVisibleSAT original visibleAssignment :=
  fun preprocess decode accept satProof =>
    ay_vtc_sat_checker_sound original solver internalAssignment
      visibleAssignment satBranch preprocess decode accept satProof

theorem ay_vtc_accepted_unsat_branch_sound
    (original solver stream finalClause unsatBranch : Prop) :
    AyVTCPreprocessArtifact original solver ->
    AyVTCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    unsatBranch ->
    AyVTCUnsat original :=
  fun preprocess replay closeFinal accept unsatProof =>
    ay_vtc_unsat_checker_sound original solver stream finalClause unsatBranch
      preprocess replay closeFinal accept unsatProof
