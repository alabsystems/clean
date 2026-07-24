-- SAT-COMP validator CLI exit-code contract core.
--
-- Public validator exits are split into accepted SAT/UNSAT and no-claim exits.
-- Only accepted SAT/UNSAT exits expose semantic SAT/UNSAT facts.  UNKNOWN,
-- parse error, checker rejection, and archive mismatch preserve audit and
-- diagnostic information without creating a semantic claim.

def AyCECConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyCECDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyCECEquisat (before after : Prop) : Prop :=
  AyCECConj (before -> after) (after -> before)

def AyCECOutcome (sat unsat : Prop) : Prop :=
  AyCECDisj sat unsat

def AyCECPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyCECDisj satFact (AyCECDisj unsatFact noClaim)

def AyCECNoClaim (exitCode audit diagnostic : Prop) : Prop :=
  AyCECConj exitCode (AyCECConj audit diagnostic)

def AyCECFailureExit
    (unknown parseError checkerReject archiveMismatch : Prop) : Prop :=
  AyCECDisj unknown
    (AyCECDisj parseError (AyCECDisj checkerReject archiveMismatch))

def AyCECExitCode
    (acceptedSat acceptedUnsat unknown parseError checkerReject
      archiveMismatch : Prop) : Prop :=
  AyCECDisj acceptedSat
    (AyCECDisj acceptedUnsat
      (AyCECFailureExit unknown parseError checkerReject archiveMismatch))

def AyCECModel (formula assignment : Prop) : Prop :=
  AyCECConj formula assignment

def AyCECUnsat (formula : Prop) : Prop :=
  formula -> False

def AyCECVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyCECModel original visibleAssignment

def AyCECSatChecker (branch visibleSat : Prop) : Prop :=
  branch -> visibleSat

def AyCECUnsatChecker (branch publicUnsat : Prop) : Prop :=
  branch -> publicUnsat

def AyCECPreprocessArtifact (original solver : Prop) : Prop :=
  AyCECEquisat original solver

def AyCECReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

def AyCECCompressed (payload : Prop) : Prop :=
  payload

def AyCECIndexed (index payload : Prop) : Prop :=
  AyCECConj index payload

theorem ay_cec_conj_intro (left right : Prop) :
    left -> right -> AyCECConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_cec_conj_left (left right : Prop) :
    AyCECConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_cec_conj_right (left right : Prop) :
    AyCECConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_cec_disj_left (left right : Prop) :
    left -> AyCECDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_cec_disj_right (left right : Prop) :
    right -> AyCECDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_cec_equisat_forward (before after : Prop) :
    AyCECEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_cec_equisat_backward (before after : Prop) :
    AyCECEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_cec_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyCECModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_cec_conj_intro formula assignment formulaProof assignmentProof

theorem ay_cec_model_formula (formula assignment : Prop) :
    AyCECModel formula assignment -> formula :=
  fun model => ay_cec_conj_left formula assignment model

theorem ay_cec_model_assignment (formula assignment : Prop) :
    AyCECModel formula assignment -> assignment :=
  fun model => ay_cec_conj_right formula assignment model

theorem ay_cec_compressed_expand (payload : Prop) :
    AyCECCompressed payload -> payload :=
  fun compressed => compressed

theorem ay_cec_compressed_pack (payload : Prop) :
    payload -> AyCECCompressed payload :=
  fun payloadProof => payloadProof

theorem ay_cec_indexed_intro (index payload : Prop) :
    index -> payload -> AyCECIndexed index payload :=
  fun indexProof payloadProof =>
    ay_cec_conj_intro index payload indexProof payloadProof

theorem ay_cec_indexed_index (index payload : Prop) :
    AyCECIndexed index payload -> index :=
  fun indexed => ay_cec_conj_left index payload indexed

theorem ay_cec_indexed_payload (index payload : Prop) :
    AyCECIndexed index payload -> payload :=
  fun indexed => ay_cec_conj_right index payload indexed

theorem ay_cec_indexed_compressed_lookup (index payload : Prop) :
    AyCECIndexed index (AyCECCompressed payload) ->
    index ->
    payload :=
  fun indexed _indexProof =>
    ay_cec_compressed_expand payload
      (ay_cec_indexed_payload index (AyCECCompressed payload) indexed)

theorem ay_cec_no_claim_intro (exitCode audit diagnostic : Prop) :
    exitCode -> audit -> diagnostic ->
    AyCECNoClaim exitCode audit diagnostic :=
  fun exitProof auditProof diagnosticProof =>
    ay_cec_conj_intro exitCode (AyCECConj audit diagnostic)
      exitProof
      (ay_cec_conj_intro audit diagnostic auditProof diagnosticProof)

theorem ay_cec_no_claim_exit (exitCode audit diagnostic : Prop) :
    AyCECNoClaim exitCode audit diagnostic -> exitCode :=
  fun noClaim =>
    ay_cec_conj_left exitCode (AyCECConj audit diagnostic) noClaim

theorem ay_cec_no_claim_audit (exitCode audit diagnostic : Prop) :
    AyCECNoClaim exitCode audit diagnostic -> audit :=
  fun noClaim =>
    ay_cec_conj_right exitCode (AyCECConj audit diagnostic) noClaim
      audit (fun auditProof _diagnosticProof => auditProof)

theorem ay_cec_no_claim_diagnostic (exitCode audit diagnostic : Prop) :
    AyCECNoClaim exitCode audit diagnostic -> diagnostic :=
  fun noClaim =>
    ay_cec_conj_right exitCode (AyCECConj audit diagnostic) noClaim
      diagnostic (fun _auditProof diagnosticProof => diagnosticProof)

theorem ay_cec_unknown_exit_no_claim
    (unknown audit diagnostic : Prop) :
    unknown -> audit -> diagnostic ->
    AyCECNoClaim unknown audit diagnostic :=
  ay_cec_no_claim_intro unknown audit diagnostic

theorem ay_cec_parse_error_exit_no_claim
    (parseError audit diagnostic : Prop) :
    parseError -> audit -> diagnostic ->
    AyCECNoClaim parseError audit diagnostic :=
  ay_cec_no_claim_intro parseError audit diagnostic

theorem ay_cec_checker_rejection_exit_no_claim
    (checkerReject audit diagnostic : Prop) :
    checkerReject -> audit -> diagnostic ->
    AyCECNoClaim checkerReject audit diagnostic :=
  ay_cec_no_claim_intro checkerReject audit diagnostic

theorem ay_cec_archive_mismatch_exit_no_claim
    (archiveMismatch audit diagnostic : Prop) :
    archiveMismatch -> audit -> diagnostic ->
    AyCECNoClaim archiveMismatch audit diagnostic :=
  ay_cec_no_claim_intro archiveMismatch audit diagnostic

theorem ay_cec_failure_exit_no_claim
    (unknown parseError checkerReject archiveMismatch audit diagnostic : Prop) :
    (unknown -> audit) ->
    (unknown -> diagnostic) ->
    (parseError -> audit) ->
    (parseError -> diagnostic) ->
    (checkerReject -> audit) ->
    (checkerReject -> diagnostic) ->
    (archiveMismatch -> audit) ->
    (archiveMismatch -> diagnostic) ->
    AyCECFailureExit unknown parseError checkerReject archiveMismatch ->
    AyCECDisj
      (AyCECNoClaim unknown audit diagnostic)
      (AyCECDisj
        (AyCECNoClaim parseError audit diagnostic)
        (AyCECDisj
          (AyCECNoClaim checkerReject audit diagnostic)
          (AyCECNoClaim archiveMismatch audit diagnostic))) :=
  fun unknownAudit unknownDiag parseAudit parseDiag rejectAudit rejectDiag
      mismatchAudit mismatchDiag failure result onUnknown onRest =>
    failure result
      (fun unknownProof =>
        onUnknown
          (ay_cec_unknown_exit_no_claim unknown audit diagnostic unknownProof
            (unknownAudit unknownProof) (unknownDiag unknownProof)))
      (fun rest1 =>
        rest1 result
          (fun parseProof =>
            onRest
              (ay_cec_disj_left
                (AyCECNoClaim parseError audit diagnostic)
                (AyCECDisj
                  (AyCECNoClaim checkerReject audit diagnostic)
                  (AyCECNoClaim archiveMismatch audit diagnostic))
                (ay_cec_parse_error_exit_no_claim parseError audit
                  diagnostic parseProof (parseAudit parseProof)
                  (parseDiag parseProof))))
          (fun rest2 =>
            rest2 result
              (fun rejectProof =>
                onRest
                  (ay_cec_disj_right
                    (AyCECNoClaim parseError audit diagnostic)
                    (AyCECDisj
                      (AyCECNoClaim checkerReject audit diagnostic)
                      (AyCECNoClaim archiveMismatch audit diagnostic))
                    (ay_cec_disj_left
                      (AyCECNoClaim checkerReject audit diagnostic)
                      (AyCECNoClaim archiveMismatch audit diagnostic)
                      (ay_cec_checker_rejection_exit_no_claim checkerReject
                        audit diagnostic rejectProof
                        (rejectAudit rejectProof)
                        (rejectDiag rejectProof)))))
              (fun mismatchProof =>
                onRest
                  (ay_cec_disj_right
                    (AyCECNoClaim parseError audit diagnostic)
                    (AyCECDisj
                      (AyCECNoClaim checkerReject audit diagnostic)
                      (AyCECNoClaim archiveMismatch audit diagnostic))
                    (ay_cec_disj_right
                      (AyCECNoClaim checkerReject audit diagnostic)
                      (AyCECNoClaim archiveMismatch audit diagnostic)
                      (ay_cec_archive_mismatch_exit_no_claim
                        archiveMismatch audit diagnostic mismatchProof
                        (mismatchAudit mismatchProof)
                        (mismatchDiag mismatchProof)))))))

theorem ay_cec_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyCECPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyCECModel solver internalAssignment ->
    AyCECVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_cec_model_intro original visibleAssignment
      (ay_cec_equisat_backward original solver preprocess
        (ay_cec_model_formula solver internalAssignment model))
      (decode (ay_cec_model_assignment solver internalAssignment model))

theorem ay_cec_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyCECPreprocessArtifact original solver ->
    AyCECUnsat solver ->
    AyCECUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_cec_equisat_forward original solver preprocess originalProof)

theorem ay_cec_replay_unsat_solver
    (solver stream finalClause : Prop) :
    AyCECReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyCECUnsat solver :=
  fun replay closeFinal streamProof solverProof =>
    closeFinal (replay streamProof solverProof)

theorem ay_cec_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyCECPreprocessArtifact original solver ->
    AyCECReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyCECUnsat original :=
  fun preprocess replay closeFinal streamProof =>
    ay_cec_preprocess_unsat_reconstruct original solver preprocess
      (ay_cec_replay_unsat_solver solver stream finalClause replay
        closeFinal streamProof)

theorem ay_cec_accepted_sat_exit_sound
    (original solver internalAssignment visibleAssignment satBranch : Prop) :
    AyCECPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyCECModel solver internalAssignment) ->
    satBranch ->
    AyCECVisibleSAT original visibleAssignment :=
  fun preprocess decode accept branchProof =>
    ay_cec_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode (accept branchProof)

theorem ay_cec_accepted_unsat_exit_sound
    (original solver stream finalClause unsatBranch : Prop) :
    AyCECPreprocessArtifact original solver ->
    AyCECReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    unsatBranch ->
    AyCECUnsat original :=
  fun preprocess replay closeFinal accept branchProof =>
    ay_cec_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal (accept branchProof)

theorem ay_cec_outcome_map
    (beforeSat afterSat beforeUnsat afterUnsat : Prop) :
    (beforeSat -> afterSat) ->
    (beforeUnsat -> afterUnsat) ->
    AyCECOutcome beforeSat beforeUnsat ->
    AyCECOutcome afterSat afterUnsat :=
  fun satMap unsatMap outcome result onSat onUnsat =>
    outcome result
      (fun satProof => onSat (satMap satProof))
      (fun unsatProof => onUnsat (unsatMap unsatProof))

theorem ay_cec_indexed_accepted_outcome_sound
    (index satBranch unsatBranch publicSat publicUnsat : Prop) :
    (satBranch -> publicSat) ->
    (unsatBranch -> publicUnsat) ->
    AyCECIndexed index
      (AyCECCompressed (AyCECOutcome satBranch unsatBranch)) ->
    index ->
    AyCECOutcome publicSat publicUnsat :=
  fun satSound unsatSound indexed indexProof =>
    ay_cec_outcome_map satBranch publicSat unsatBranch publicUnsat
      satSound unsatSound
      (ay_cec_indexed_compressed_lookup index
        (AyCECOutcome satBranch unsatBranch) indexed indexProof)

theorem ay_cec_exit_code_dispatch
    (acceptedSat acceptedUnsat unknown parseError checkerReject
      archiveMismatch publicSat publicUnsat noClaim : Prop) :
    (acceptedSat -> publicSat) ->
    (acceptedUnsat -> publicUnsat) ->
    (AyCECFailureExit unknown parseError checkerReject archiveMismatch ->
      noClaim) ->
    AyCECExitCode acceptedSat acceptedUnsat unknown parseError checkerReject
      archiveMismatch ->
    AyCECPublicResult publicSat publicUnsat noClaim :=
  fun satSound unsatSound failureNoClaim exit result onSat onRest =>
    exit result
      (fun satProof => onSat (satSound satProof))
      (fun rest =>
        rest result
          (fun unsatProof =>
            onRest
              (ay_cec_disj_left publicUnsat noClaim
                (unsatSound unsatProof)))
          (fun failureProof =>
            onRest
              (ay_cec_disj_right publicUnsat noClaim
                (failureNoClaim failureProof))))

theorem ay_cec_no_claim_public_result
    (satFact unsatFact exitCode audit diagnostic : Prop) :
    AyCECNoClaim exitCode audit diagnostic ->
    AyCECPublicResult satFact unsatFact
      (AyCECNoClaim exitCode audit diagnostic) :=
  fun noClaim =>
    ay_cec_disj_right satFact
      (AyCECDisj unsatFact
        (AyCECNoClaim exitCode audit diagnostic))
      (ay_cec_disj_right unsatFact
        (AyCECNoClaim exitCode audit diagnostic)
        noClaim)
