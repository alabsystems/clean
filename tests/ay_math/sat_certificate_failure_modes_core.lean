-- SAT-COMP certificate failure-mode semantics core.
--
-- Failure modes are deliberately separated from semantic SAT/UNSAT claims.
-- Accepted branches dispatch to the usual checker obligations; parse failure,
-- missing certificates, checker rejection, UNKNOWN, and archive inconsistency
-- produce only explicit no-claim/failure records.

def AyCFMConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyCFMDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCFMEquisat (before after : Prop) : Prop :=
  AyCFMConj (before -> after) (after -> before)

def AyCFMOutcome (sat unsat : Prop) : Prop :=
  AyCFMDisj sat unsat

def AyCFMValidated (satFact unsatFact noClaim : Prop) : Prop :=
  AyCFMDisj satFact (AyCFMDisj unsatFact noClaim)

def AyCFMFailure
    (parseFailure missingCert checkerReject unknown archiveBad : Prop) : Prop :=
  AyCFMDisj parseFailure
    (AyCFMDisj missingCert
      (AyCFMDisj checkerReject (AyCFMDisj unknown archiveBad)))

def AyCFMNoClaim (reason archiveState : Prop) : Prop :=
  AyCFMConj reason archiveState

def AyCFMModel (formula assignment : Prop) : Prop :=
  AyCFMConj formula assignment

def AyCFMUnsat (formula : Prop) : Prop :=
  formula -> False

def AyCFMVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyCFMModel original visibleAssignment

def AyCFMCompressed (payload : Prop) : Prop :=
  payload

def AyCFMIndexed (index payload : Prop) : Prop :=
  AyCFMConj index payload

def AyCFMSatChecker (branch visibleSat : Prop) : Prop :=
  branch -> visibleSat

def AyCFMUnsatChecker (branch publicUnsat : Prop) : Prop :=
  branch -> publicUnsat

def AyCFMReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

def AyCFMPreprocessArtifact (original solver : Prop) : Prop :=
  AyCFMEquisat original solver

def AyCFMCertificateAvailable (certId archiveKey : Prop) : Prop :=
  AyCFMConj certId archiveKey

theorem ay_cfm_conj_intro (left right : Prop) :
    left -> right -> AyCFMConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_cfm_conj_left (left right : Prop) :
    AyCFMConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_cfm_conj_right (left right : Prop) :
    AyCFMConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_cfm_disj_left (left right : Prop) :
    left -> AyCFMDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_cfm_disj_right (left right : Prop) :
    right -> AyCFMDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_cfm_equisat_forward (before after : Prop) :
    AyCFMEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_cfm_equisat_backward (before after : Prop) :
    AyCFMEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_cfm_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyCFMModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_cfm_conj_intro formula assignment formulaProof assignmentProof

theorem ay_cfm_model_formula (formula assignment : Prop) :
    AyCFMModel formula assignment -> formula :=
  fun model => ay_cfm_conj_left formula assignment model

theorem ay_cfm_model_assignment (formula assignment : Prop) :
    AyCFMModel formula assignment -> assignment :=
  fun model => ay_cfm_conj_right formula assignment model

theorem ay_cfm_compressed_expand (payload : Prop) :
    AyCFMCompressed payload -> payload :=
  fun compressed => compressed

theorem ay_cfm_compressed_pack (payload : Prop) :
    payload -> AyCFMCompressed payload :=
  fun payloadProof => payloadProof

theorem ay_cfm_indexed_intro (index payload : Prop) :
    index -> payload -> AyCFMIndexed index payload :=
  fun indexProof payloadProof =>
    ay_cfm_conj_intro index payload indexProof payloadProof

theorem ay_cfm_indexed_index (index payload : Prop) :
    AyCFMIndexed index payload -> index :=
  fun indexed => ay_cfm_conj_left index payload indexed

theorem ay_cfm_indexed_payload (index payload : Prop) :
    AyCFMIndexed index payload -> payload :=
  fun indexed => ay_cfm_conj_right index payload indexed

theorem ay_cfm_indexed_compressed_lookup (index payload : Prop) :
    AyCFMIndexed index (AyCFMCompressed payload) ->
    index ->
    payload :=
  fun indexed _indexProof =>
    ay_cfm_compressed_expand payload
      (ay_cfm_indexed_payload index (AyCFMCompressed payload) indexed)

theorem ay_cfm_certificate_id (certId archiveKey : Prop) :
    AyCFMCertificateAvailable certId archiveKey -> certId :=
  ay_cfm_conj_left certId archiveKey

theorem ay_cfm_certificate_archive (certId archiveKey : Prop) :
    AyCFMCertificateAvailable certId archiveKey -> archiveKey :=
  ay_cfm_conj_right certId archiveKey

theorem ay_cfm_outcome_map
    (beforeSat afterSat beforeUnsat afterUnsat : Prop) :
    (beforeSat -> afterSat) ->
    (beforeUnsat -> afterUnsat) ->
    AyCFMOutcome beforeSat beforeUnsat ->
    AyCFMOutcome afterSat afterUnsat :=
  fun satMap unsatMap outcome result onSat onUnsat =>
    outcome result
      (fun satProof => onSat (satMap satProof))
      (fun unsatProof => onUnsat (unsatMap unsatProof))

theorem ay_cfm_no_claim_intro (reason archiveState : Prop) :
    reason -> archiveState -> AyCFMNoClaim reason archiveState :=
  ay_cfm_conj_intro reason archiveState

theorem ay_cfm_no_claim_reason (reason archiveState : Prop) :
    AyCFMNoClaim reason archiveState -> reason :=
  ay_cfm_conj_left reason archiveState

theorem ay_cfm_no_claim_archive (reason archiveState : Prop) :
    AyCFMNoClaim reason archiveState -> archiveState :=
  ay_cfm_conj_right reason archiveState

theorem ay_cfm_parse_failure_no_claim
    (parseFailure archiveState : Prop) :
    parseFailure -> archiveState ->
    AyCFMNoClaim parseFailure archiveState :=
  ay_cfm_no_claim_intro parseFailure archiveState

theorem ay_cfm_missing_certificate_no_claim
    (missingCert archiveState : Prop) :
    missingCert -> archiveState ->
    AyCFMNoClaim missingCert archiveState :=
  ay_cfm_no_claim_intro missingCert archiveState

theorem ay_cfm_checker_rejection_no_claim
    (checkerReject archiveState : Prop) :
    checkerReject -> archiveState ->
    AyCFMNoClaim checkerReject archiveState :=
  ay_cfm_no_claim_intro checkerReject archiveState

theorem ay_cfm_unknown_no_claim
    (unknown archiveState : Prop) :
    unknown -> archiveState -> AyCFMNoClaim unknown archiveState :=
  ay_cfm_no_claim_intro unknown archiveState

theorem ay_cfm_archive_inconsistency_no_claim
    (archiveBad archiveState : Prop) :
    archiveBad -> archiveState ->
    AyCFMNoClaim archiveBad archiveState :=
  ay_cfm_no_claim_intro archiveBad archiveState

theorem ay_cfm_failure_no_claim
    (parseFailure missingCert checkerReject unknown archiveBad archiveState :
      Prop) :
    (parseFailure -> archiveState) ->
    (missingCert -> archiveState) ->
    (checkerReject -> archiveState) ->
    (unknown -> archiveState) ->
    (archiveBad -> archiveState) ->
    AyCFMFailure parseFailure missingCert checkerReject unknown archiveBad ->
    AyCFMDisj
      (AyCFMNoClaim parseFailure archiveState)
      (AyCFMDisj
        (AyCFMNoClaim missingCert archiveState)
        (AyCFMDisj
          (AyCFMNoClaim checkerReject archiveState)
          (AyCFMDisj
            (AyCFMNoClaim unknown archiveState)
            (AyCFMNoClaim archiveBad archiveState)))) :=
  fun parseArchive missingArchive rejectArchive unknownArchive badArchive
      failure result onParse onRest =>
    failure result
      (fun parseProof =>
        onParse
          (ay_cfm_parse_failure_no_claim parseFailure archiveState
            parseProof (parseArchive parseProof)))
      (fun rest1 =>
        rest1 result
          (fun missingProof =>
            onRest
              (ay_cfm_disj_left
                (AyCFMNoClaim missingCert archiveState)
                (AyCFMDisj
                  (AyCFMNoClaim checkerReject archiveState)
                  (AyCFMDisj
                    (AyCFMNoClaim unknown archiveState)
                    (AyCFMNoClaim archiveBad archiveState)))
                (ay_cfm_missing_certificate_no_claim missingCert archiveState
                  missingProof (missingArchive missingProof))))
          (fun rest2 =>
            rest2 result
              (fun rejectProof =>
                onRest
                  (ay_cfm_disj_right
                    (AyCFMNoClaim missingCert archiveState)
                    (AyCFMDisj
                      (AyCFMNoClaim checkerReject archiveState)
                      (AyCFMDisj
                        (AyCFMNoClaim unknown archiveState)
                        (AyCFMNoClaim archiveBad archiveState)))
                    (ay_cfm_disj_left
                      (AyCFMNoClaim checkerReject archiveState)
                      (AyCFMDisj
                        (AyCFMNoClaim unknown archiveState)
                        (AyCFMNoClaim archiveBad archiveState))
                      (ay_cfm_checker_rejection_no_claim checkerReject
                        archiveState rejectProof
                        (rejectArchive rejectProof)))))
              (fun rest3 =>
                rest3 result
                  (fun unknownProof =>
                    onRest
                      (ay_cfm_disj_right
                        (AyCFMNoClaim missingCert archiveState)
                        (AyCFMDisj
                          (AyCFMNoClaim checkerReject archiveState)
                          (AyCFMDisj
                            (AyCFMNoClaim unknown archiveState)
                            (AyCFMNoClaim archiveBad archiveState)))
                        (ay_cfm_disj_right
                          (AyCFMNoClaim checkerReject archiveState)
                          (AyCFMDisj
                            (AyCFMNoClaim unknown archiveState)
                            (AyCFMNoClaim archiveBad archiveState))
                          (ay_cfm_disj_left
                            (AyCFMNoClaim unknown archiveState)
                            (AyCFMNoClaim archiveBad archiveState)
                            (ay_cfm_unknown_no_claim unknown archiveState
                              unknownProof
                              (unknownArchive unknownProof))))))
                  (fun badProof =>
                    onRest
                      (ay_cfm_disj_right
                        (AyCFMNoClaim missingCert archiveState)
                        (AyCFMDisj
                          (AyCFMNoClaim checkerReject archiveState)
                          (AyCFMDisj
                            (AyCFMNoClaim unknown archiveState)
                            (AyCFMNoClaim archiveBad archiveState)))
                        (ay_cfm_disj_right
                          (AyCFMNoClaim checkerReject archiveState)
                          (AyCFMDisj
                            (AyCFMNoClaim unknown archiveState)
                            (AyCFMNoClaim archiveBad archiveState))
                          (ay_cfm_disj_right
                            (AyCFMNoClaim unknown archiveState)
                            (AyCFMNoClaim archiveBad archiveState)
                            (ay_cfm_archive_inconsistency_no_claim
                              archiveBad archiveState badProof
                              (badArchive badProof)))))))))

theorem ay_cfm_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyCFMPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyCFMModel solver internalAssignment ->
    AyCFMVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_cfm_model_intro original visibleAssignment
      (ay_cfm_equisat_backward original solver preprocess
        (ay_cfm_model_formula solver internalAssignment model))
      (decode (ay_cfm_model_assignment solver internalAssignment model))

theorem ay_cfm_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyCFMPreprocessArtifact original solver ->
    AyCFMUnsat solver ->
    AyCFMUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_cfm_equisat_forward original solver preprocess originalProof)

theorem ay_cfm_replay_unsat_solver
    (solver stream finalClause : Prop) :
    AyCFMReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyCFMUnsat solver :=
  fun replay closeFinal streamProof solverProof =>
    closeFinal (replay streamProof solverProof)

theorem ay_cfm_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyCFMPreprocessArtifact original solver ->
    AyCFMReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyCFMUnsat original :=
  fun preprocess replay closeFinal streamProof =>
    ay_cfm_preprocess_unsat_reconstruct original solver preprocess
      (ay_cfm_replay_unsat_solver solver stream finalClause replay
        closeFinal streamProof)

theorem ay_cfm_sat_checker_dispatch
    (original solver internalAssignment visibleAssignment satBranch : Prop) :
    AyCFMPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyCFMModel solver internalAssignment) ->
    AyCFMSatChecker satBranch
      (AyCFMVisibleSAT original visibleAssignment) :=
  fun preprocess decode accept branchProof =>
    ay_cfm_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode (accept branchProof)

theorem ay_cfm_unsat_checker_dispatch
    (original solver stream finalClause unsatBranch : Prop) :
    AyCFMPreprocessArtifact original solver ->
    AyCFMReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyCFMUnsatChecker unsatBranch (AyCFMUnsat original) :=
  fun preprocess replay closeFinal accept branchProof =>
    ay_cfm_replay_unsat_public original solver stream finalClause
      preprocess replay closeFinal (accept branchProof)

theorem ay_cfm_accepted_outcome_dispatch
    (satBranch unsatBranch publicSat publicUnsat : Prop) :
    AyCFMSatChecker satBranch publicSat ->
    AyCFMUnsatChecker unsatBranch publicUnsat ->
    AyCFMOutcome satBranch unsatBranch ->
    AyCFMOutcome publicSat publicUnsat :=
  fun satChecker unsatChecker =>
    ay_cfm_outcome_map satBranch publicSat unsatBranch publicUnsat
      satChecker unsatChecker

theorem ay_cfm_indexed_accepted_dispatch
    (index satBranch unsatBranch publicSat publicUnsat : Prop) :
    AyCFMSatChecker satBranch publicSat ->
    AyCFMUnsatChecker unsatBranch publicUnsat ->
    AyCFMIndexed index
      (AyCFMCompressed (AyCFMOutcome satBranch unsatBranch)) ->
    index ->
    AyCFMOutcome publicSat publicUnsat :=
  fun satChecker unsatChecker indexed indexProof =>
    ay_cfm_accepted_outcome_dispatch satBranch unsatBranch publicSat
      publicUnsat satChecker unsatChecker
      (ay_cfm_indexed_compressed_lookup index
        (AyCFMOutcome satBranch unsatBranch) indexed indexProof)

theorem ay_cfm_accepted_sat_certificate_sound
    (original solver internalAssignment visibleAssignment satBranch : Prop) :
    AyCFMPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyCFMModel solver internalAssignment) ->
    satBranch ->
    AyCFMVisibleSAT original visibleAssignment :=
  fun preprocess decode accept branchProof =>
    ay_cfm_sat_checker_dispatch original solver internalAssignment
      visibleAssignment satBranch preprocess decode accept branchProof

theorem ay_cfm_accepted_unsat_certificate_sound
    (original solver stream finalClause unsatBranch : Prop) :
    AyCFMPreprocessArtifact original solver ->
    AyCFMReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    unsatBranch ->
    AyCFMUnsat original :=
  fun preprocess replay closeFinal accept branchProof =>
    ay_cfm_unsat_checker_dispatch original solver stream finalClause
      unsatBranch preprocess replay closeFinal accept branchProof

theorem ay_cfm_rejected_or_unavailable_validated_no_claim
    (satFact unsatFact reason archiveState : Prop) :
    AyCFMNoClaim reason archiveState ->
    AyCFMValidated satFact unsatFact
      (AyCFMNoClaim reason archiveState) :=
  fun noClaim =>
    ay_cfm_disj_right satFact
      (AyCFMDisj unsatFact (AyCFMNoClaim reason archiveState))
      (ay_cfm_disj_right unsatFact (AyCFMNoClaim reason archiveState)
        noClaim)
