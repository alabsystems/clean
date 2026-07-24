-- SAT-COMP validator error-code contract core.
--
-- Public validator codes are separated into accepted SAT/UNSAT and no-claim
-- cases.  Parser errors, missing certificates, checker rejection, archive
-- mismatch, and UNKNOWN expose only explicit no-claim states.

def AyECCConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyECCDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyECCEquisat (before after : Prop) : Prop :=
  AyECCConj (before -> after) (after -> before)

def AyECCOutcome (sat unsat : Prop) : Prop :=
  AyECCDisj sat unsat

def AyECCPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyECCDisj satFact (AyECCDisj unsatFact noClaim)

def AyECCNoClaim (code archiveState : Prop) : Prop :=
  AyECCConj code archiveState

def AyECCErrorCode
    (parserError missingCert checkerReject archiveMismatch unknown : Prop) :
    Prop :=
  AyECCDisj parserError
    (AyECCDisj missingCert
      (AyECCDisj checkerReject (AyECCDisj archiveMismatch unknown)))

def AyECCAcceptedCode (acceptedSat acceptedUnsat : Prop) : Prop :=
  AyECCDisj acceptedSat acceptedUnsat

def AyECCValidatorCode
    (acceptedSat acceptedUnsat parserError missingCert checkerReject
      archiveMismatch unknown : Prop) : Prop :=
  AyECCDisj acceptedSat
    (AyECCDisj acceptedUnsat
      (AyECCErrorCode parserError missingCert checkerReject archiveMismatch
        unknown))

def AyECCModel (formula assignment : Prop) : Prop :=
  AyECCConj formula assignment

def AyECCUnsat (formula : Prop) : Prop :=
  formula -> False

def AyECCVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyECCModel original visibleAssignment

def AyECCSatChecker (branch visibleSat : Prop) : Prop :=
  branch -> visibleSat

def AyECCUnsatChecker (branch publicUnsat : Prop) : Prop :=
  branch -> publicUnsat

def AyECCPreprocessArtifact (original solver : Prop) : Prop :=
  AyECCEquisat original solver

def AyECCReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_ecc_conj_intro (left right : Prop) :
    left -> right -> AyECCConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_ecc_conj_left (left right : Prop) :
    AyECCConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_ecc_conj_right (left right : Prop) :
    AyECCConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_ecc_disj_left (left right : Prop) :
    left -> AyECCDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_ecc_disj_right (left right : Prop) :
    right -> AyECCDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_ecc_equisat_forward (before after : Prop) :
    AyECCEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_ecc_equisat_backward (before after : Prop) :
    AyECCEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_ecc_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyECCModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_ecc_conj_intro formula assignment formulaProof assignmentProof

theorem ay_ecc_model_formula (formula assignment : Prop) :
    AyECCModel formula assignment -> formula :=
  fun model => ay_ecc_conj_left formula assignment model

theorem ay_ecc_model_assignment (formula assignment : Prop) :
    AyECCModel formula assignment -> assignment :=
  fun model => ay_ecc_conj_right formula assignment model

theorem ay_ecc_no_claim_intro (code archiveState : Prop) :
    code -> archiveState -> AyECCNoClaim code archiveState :=
  ay_ecc_conj_intro code archiveState

theorem ay_ecc_no_claim_code (code archiveState : Prop) :
    AyECCNoClaim code archiveState -> code :=
  ay_ecc_conj_left code archiveState

theorem ay_ecc_no_claim_archive (code archiveState : Prop) :
    AyECCNoClaim code archiveState -> archiveState :=
  ay_ecc_conj_right code archiveState

theorem ay_ecc_parser_error_no_claim
    (parserError archiveState : Prop) :
    parserError -> archiveState ->
    AyECCNoClaim parserError archiveState :=
  ay_ecc_no_claim_intro parserError archiveState

theorem ay_ecc_missing_certificate_no_claim
    (missingCert archiveState : Prop) :
    missingCert -> archiveState ->
    AyECCNoClaim missingCert archiveState :=
  ay_ecc_no_claim_intro missingCert archiveState

theorem ay_ecc_checker_rejection_no_claim
    (checkerReject archiveState : Prop) :
    checkerReject -> archiveState ->
    AyECCNoClaim checkerReject archiveState :=
  ay_ecc_no_claim_intro checkerReject archiveState

theorem ay_ecc_archive_mismatch_no_claim
    (archiveMismatch archiveState : Prop) :
    archiveMismatch -> archiveState ->
    AyECCNoClaim archiveMismatch archiveState :=
  ay_ecc_no_claim_intro archiveMismatch archiveState

theorem ay_ecc_unknown_no_claim
    (unknown archiveState : Prop) :
    unknown -> archiveState -> AyECCNoClaim unknown archiveState :=
  ay_ecc_no_claim_intro unknown archiveState

theorem ay_ecc_error_code_no_claim
    (parserError missingCert checkerReject archiveMismatch unknown
      archiveState : Prop) :
    (parserError -> archiveState) ->
    (missingCert -> archiveState) ->
    (checkerReject -> archiveState) ->
    (archiveMismatch -> archiveState) ->
    (unknown -> archiveState) ->
    AyECCErrorCode parserError missingCert checkerReject archiveMismatch
      unknown ->
    AyECCDisj
      (AyECCNoClaim parserError archiveState)
      (AyECCDisj
        (AyECCNoClaim missingCert archiveState)
        (AyECCDisj
          (AyECCNoClaim checkerReject archiveState)
          (AyECCDisj
            (AyECCNoClaim archiveMismatch archiveState)
            (AyECCNoClaim unknown archiveState)))) :=
  fun parserArchive missingArchive rejectArchive mismatchArchive
      unknownArchive code result onParser onRest =>
    code result
      (fun parserProof =>
        onParser
          (ay_ecc_parser_error_no_claim parserError archiveState parserProof
            (parserArchive parserProof)))
      (fun rest1 =>
        rest1 result
          (fun missingProof =>
            onRest
              (ay_ecc_disj_left
                (AyECCNoClaim missingCert archiveState)
                (AyECCDisj
                  (AyECCNoClaim checkerReject archiveState)
                  (AyECCDisj
                    (AyECCNoClaim archiveMismatch archiveState)
                    (AyECCNoClaim unknown archiveState)))
                (ay_ecc_missing_certificate_no_claim missingCert archiveState
                  missingProof (missingArchive missingProof))))
          (fun rest2 =>
            rest2 result
              (fun rejectProof =>
                onRest
                  (ay_ecc_disj_right
                    (AyECCNoClaim missingCert archiveState)
                    (AyECCDisj
                      (AyECCNoClaim checkerReject archiveState)
                      (AyECCDisj
                        (AyECCNoClaim archiveMismatch archiveState)
                        (AyECCNoClaim unknown archiveState)))
                    (ay_ecc_disj_left
                      (AyECCNoClaim checkerReject archiveState)
                      (AyECCDisj
                        (AyECCNoClaim archiveMismatch archiveState)
                        (AyECCNoClaim unknown archiveState))
                      (ay_ecc_checker_rejection_no_claim checkerReject
                        archiveState rejectProof
                        (rejectArchive rejectProof)))))
              (fun rest3 =>
                rest3 result
                  (fun mismatchProof =>
                    onRest
                      (ay_ecc_disj_right
                        (AyECCNoClaim missingCert archiveState)
                        (AyECCDisj
                          (AyECCNoClaim checkerReject archiveState)
                          (AyECCDisj
                            (AyECCNoClaim archiveMismatch archiveState)
                            (AyECCNoClaim unknown archiveState)))
                        (ay_ecc_disj_right
                          (AyECCNoClaim checkerReject archiveState)
                          (AyECCDisj
                            (AyECCNoClaim archiveMismatch archiveState)
                            (AyECCNoClaim unknown archiveState))
                          (ay_ecc_disj_left
                            (AyECCNoClaim archiveMismatch archiveState)
                            (AyECCNoClaim unknown archiveState)
                            (ay_ecc_archive_mismatch_no_claim
                              archiveMismatch archiveState mismatchProof
                              (mismatchArchive mismatchProof))))))
                  (fun unknownProof =>
                    onRest
                      (ay_ecc_disj_right
                        (AyECCNoClaim missingCert archiveState)
                        (AyECCDisj
                          (AyECCNoClaim checkerReject archiveState)
                          (AyECCDisj
                            (AyECCNoClaim archiveMismatch archiveState)
                            (AyECCNoClaim unknown archiveState)))
                        (ay_ecc_disj_right
                          (AyECCNoClaim checkerReject archiveState)
                          (AyECCDisj
                            (AyECCNoClaim archiveMismatch archiveState)
                            (AyECCNoClaim unknown archiveState))
                          (ay_ecc_disj_right
                            (AyECCNoClaim archiveMismatch archiveState)
                            (AyECCNoClaim unknown archiveState)
                            (ay_ecc_unknown_no_claim unknown archiveState
                              unknownProof
                              (unknownArchive unknownProof)))))))))

theorem ay_ecc_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyECCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyECCModel solver internalAssignment ->
    AyECCVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_ecc_model_intro original visibleAssignment
      (ay_ecc_equisat_backward original solver preprocess
        (ay_ecc_model_formula solver internalAssignment model))
      (decode (ay_ecc_model_assignment solver internalAssignment model))

theorem ay_ecc_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyECCPreprocessArtifact original solver ->
    AyECCUnsat solver ->
    AyECCUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_ecc_equisat_forward original solver preprocess originalProof)

theorem ay_ecc_replay_unsat_solver
    (solver stream finalClause : Prop) :
    AyECCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyECCUnsat solver :=
  fun replay closeFinal streamProof solverProof =>
    closeFinal (replay streamProof solverProof)

theorem ay_ecc_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyECCPreprocessArtifact original solver ->
    AyECCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyECCUnsat original :=
  fun preprocess replay closeFinal streamProof =>
    ay_ecc_preprocess_unsat_reconstruct original solver preprocess
      (ay_ecc_replay_unsat_solver solver stream finalClause replay
        closeFinal streamProof)

theorem ay_ecc_accepted_sat_sound
    (original solver internalAssignment visibleAssignment satBranch : Prop) :
    AyECCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyECCModel solver internalAssignment) ->
    satBranch ->
    AyECCVisibleSAT original visibleAssignment :=
  fun preprocess decode accept branchProof =>
    ay_ecc_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode (accept branchProof)

theorem ay_ecc_accepted_unsat_sound
    (original solver stream finalClause unsatBranch : Prop) :
    AyECCPreprocessArtifact original solver ->
    AyECCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    unsatBranch ->
    AyECCUnsat original :=
  fun preprocess replay closeFinal accept branchProof =>
    ay_ecc_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal (accept branchProof)

theorem ay_ecc_accepted_code_dispatch
    (acceptedSat acceptedUnsat publicSat publicUnsat : Prop) :
    (acceptedSat -> publicSat) ->
    (acceptedUnsat -> publicUnsat) ->
    AyECCAcceptedCode acceptedSat acceptedUnsat ->
    AyECCOutcome publicSat publicUnsat :=
  fun satSound unsatSound accepted result onSat onUnsat =>
    accepted result
      (fun satProof => onSat (satSound satProof))
      (fun unsatProof => onUnsat (unsatSound unsatProof))

theorem ay_ecc_validator_code_dispatch
    (acceptedSat acceptedUnsat parserError missingCert checkerReject
      archiveMismatch unknown publicSat publicUnsat noClaim : Prop) :
    (acceptedSat -> publicSat) ->
    (acceptedUnsat -> publicUnsat) ->
    (AyECCErrorCode parserError missingCert checkerReject archiveMismatch
      unknown -> noClaim) ->
    AyECCValidatorCode acceptedSat acceptedUnsat parserError missingCert
      checkerReject archiveMismatch unknown ->
    AyECCPublicResult publicSat publicUnsat noClaim :=
  fun satSound unsatSound errorNoClaim code result onSat onRest =>
    code result
      (fun satProof => onSat (satSound satProof))
      (fun rest =>
        rest result
          (fun unsatProof =>
            onRest
              (ay_ecc_disj_left publicUnsat noClaim
                (unsatSound unsatProof)))
          (fun errorProof =>
            onRest
              (ay_ecc_disj_right publicUnsat noClaim
                (errorNoClaim errorProof))))

theorem ay_ecc_error_code_validated_no_claim
    (satFact unsatFact code archiveState : Prop) :
    AyECCNoClaim code archiveState ->
    AyECCPublicResult satFact unsatFact
      (AyECCNoClaim code archiveState) :=
  fun noClaim =>
    ay_ecc_disj_right satFact
      (AyECCDisj unsatFact (AyECCNoClaim code archiveState))
      (ay_ecc_disj_right unsatFact (AyECCNoClaim code archiveState)
        noClaim)
