-- SAT-COMP validator report contract core.
--
-- A compact public report carries an exit code, artifact ids, checker result,
-- audit digest, and optional diagnostic.  Accepted SAT/UNSAT reports expose
-- semantic facts; diagnostic reports preserve audit and diagnostic information
-- without exposing SAT/UNSAT claims.

def AyVRCConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVRCDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVRCEquisat (before after : Prop) : Prop :=
  AyVRCConj (before -> after) (after -> before)

def AyVRCOutcome (sat unsat : Prop) : Prop :=
  AyVRCDisj sat unsat

def AyVRCPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVRCDisj satFact (AyVRCDisj unsatFact noClaim)

def AyVRCArtifacts (certId archiveKey : Prop) : Prop :=
  AyVRCConj certId archiveKey

def AyVRCReport (exitCode artifacts checkerResult audit diagnostic : Prop) :
    Prop :=
  AyVRCConj exitCode
    (AyVRCConj artifacts (AyVRCConj checkerResult
      (AyVRCConj audit diagnostic)))

def AyVRCNoClaim (exitCode audit diagnostic : Prop) : Prop :=
  AyVRCConj exitCode (AyVRCConj audit diagnostic)

def AyVRCDiagnosticExit
    (unknown parseError checkerReject archiveMismatch : Prop) : Prop :=
  AyVRCDisj unknown
    (AyVRCDisj parseError (AyVRCDisj checkerReject archiveMismatch))

def AyVRCModel (formula assignment : Prop) : Prop :=
  AyVRCConj formula assignment

def AyVRCUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVRCVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVRCModel original visibleAssignment

def AyVRCPreprocessArtifact (original solver : Prop) : Prop :=
  AyVRCEquisat original solver

def AyVRCReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

def AyVRCSatChecker (branch visibleSat : Prop) : Prop :=
  branch -> visibleSat

def AyVRCUnsatChecker (branch publicUnsat : Prop) : Prop :=
  branch -> publicUnsat

theorem ay_vrc_conj_intro (left right : Prop) :
    left -> right -> AyVRCConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vrc_conj_left (left right : Prop) :
    AyVRCConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vrc_conj_right (left right : Prop) :
    AyVRCConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vrc_disj_left (left right : Prop) :
    left -> AyVRCDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vrc_disj_right (left right : Prop) :
    right -> AyVRCDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vrc_equisat_forward (before after : Prop) :
    AyVRCEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vrc_equisat_backward (before after : Prop) :
    AyVRCEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vrc_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVRCModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vrc_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vrc_model_formula (formula assignment : Prop) :
    AyVRCModel formula assignment -> formula :=
  fun model => ay_vrc_conj_left formula assignment model

theorem ay_vrc_model_assignment (formula assignment : Prop) :
    AyVRCModel formula assignment -> assignment :=
  fun model => ay_vrc_conj_right formula assignment model

theorem ay_vrc_artifacts_intro (certId archiveKey : Prop) :
    certId -> archiveKey -> AyVRCArtifacts certId archiveKey :=
  ay_vrc_conj_intro certId archiveKey

theorem ay_vrc_artifacts_cert (certId archiveKey : Prop) :
    AyVRCArtifacts certId archiveKey -> certId :=
  ay_vrc_conj_left certId archiveKey

theorem ay_vrc_artifacts_archive (certId archiveKey : Prop) :
    AyVRCArtifacts certId archiveKey -> archiveKey :=
  ay_vrc_conj_right certId archiveKey

theorem ay_vrc_report_intro
    (exitCode artifacts checkerResult audit diagnostic : Prop) :
    exitCode -> artifacts -> checkerResult -> audit -> diagnostic ->
    AyVRCReport exitCode artifacts checkerResult audit diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vrc_conj_intro exitCode
      (AyVRCConj artifacts (AyVRCConj checkerResult
        (AyVRCConj audit diagnostic)))
      exitProof
      (ay_vrc_conj_intro artifacts
        (AyVRCConj checkerResult (AyVRCConj audit diagnostic))
        artifactsProof
        (ay_vrc_conj_intro checkerResult (AyVRCConj audit diagnostic)
          checkerProof
          (ay_vrc_conj_intro audit diagnostic auditProof diagnosticProof)))

theorem ay_vrc_report_exit
    (exitCode artifacts checkerResult audit diagnostic : Prop) :
    AyVRCReport exitCode artifacts checkerResult audit diagnostic ->
    exitCode :=
  fun report =>
    ay_vrc_conj_left exitCode
      (AyVRCConj artifacts (AyVRCConj checkerResult
        (AyVRCConj audit diagnostic)))
      report

theorem ay_vrc_report_artifacts
    (exitCode artifacts checkerResult audit diagnostic : Prop) :
    AyVRCReport exitCode artifacts checkerResult audit diagnostic ->
    artifacts :=
  fun report =>
    ay_vrc_conj_right exitCode
      (AyVRCConj artifacts (AyVRCConj checkerResult
        (AyVRCConj audit diagnostic)))
      report artifacts (fun artifactsProof _tail => artifactsProof)

theorem ay_vrc_report_checker
    (exitCode artifacts checkerResult audit diagnostic : Prop) :
    AyVRCReport exitCode artifacts checkerResult audit diagnostic ->
    checkerResult :=
  fun report =>
    ay_vrc_conj_right exitCode
      (AyVRCConj artifacts (AyVRCConj checkerResult
        (AyVRCConj audit diagnostic)))
      report checkerResult
      (fun _artifactsProof tail =>
        tail checkerResult (fun checkerProof _auditTail => checkerProof))

theorem ay_vrc_report_audit
    (exitCode artifacts checkerResult audit diagnostic : Prop) :
    AyVRCReport exitCode artifacts checkerResult audit diagnostic ->
    audit :=
  fun report =>
    ay_vrc_conj_right exitCode
      (AyVRCConj artifacts (AyVRCConj checkerResult
        (AyVRCConj audit diagnostic)))
      report audit
      (fun _artifactsProof tail =>
        tail audit
          (fun _checkerProof auditTail =>
            auditTail audit (fun auditProof _diagnosticProof => auditProof)))

theorem ay_vrc_report_diagnostic
    (exitCode artifacts checkerResult audit diagnostic : Prop) :
    AyVRCReport exitCode artifacts checkerResult audit diagnostic ->
    diagnostic :=
  fun report =>
    ay_vrc_conj_right exitCode
      (AyVRCConj artifacts (AyVRCConj checkerResult
        (AyVRCConj audit diagnostic)))
      report diagnostic
      (fun _artifactsProof tail =>
        tail diagnostic
          (fun _checkerProof auditTail =>
            auditTail diagnostic
              (fun _auditProof diagnosticProof => diagnosticProof)))

theorem ay_vrc_no_claim_intro (exitCode audit diagnostic : Prop) :
    exitCode -> audit -> diagnostic ->
    AyVRCNoClaim exitCode audit diagnostic :=
  fun exitProof auditProof diagnosticProof =>
    ay_vrc_conj_intro exitCode (AyVRCConj audit diagnostic)
      exitProof
      (ay_vrc_conj_intro audit diagnostic auditProof diagnosticProof)

theorem ay_vrc_no_claim_audit (exitCode audit diagnostic : Prop) :
    AyVRCNoClaim exitCode audit diagnostic -> audit :=
  fun noClaim =>
    ay_vrc_conj_right exitCode (AyVRCConj audit diagnostic) noClaim
      audit (fun auditProof _diagnosticProof => auditProof)

theorem ay_vrc_no_claim_diagnostic (exitCode audit diagnostic : Prop) :
    AyVRCNoClaim exitCode audit diagnostic -> diagnostic :=
  fun noClaim =>
    ay_vrc_conj_right exitCode (AyVRCConj audit diagnostic) noClaim
      diagnostic (fun _auditProof diagnosticProof => diagnosticProof)

theorem ay_vrc_diagnostic_report_no_claim
    (exitCode artifacts checkerResult audit diagnostic : Prop) :
    AyVRCReport exitCode artifacts checkerResult audit diagnostic ->
    AyVRCNoClaim exitCode audit diagnostic :=
  fun report =>
    ay_vrc_no_claim_intro exitCode audit diagnostic
      (ay_vrc_report_exit exitCode artifacts checkerResult audit diagnostic
        report)
      (ay_vrc_report_audit exitCode artifacts checkerResult audit diagnostic
        report)
      (ay_vrc_report_diagnostic exitCode artifacts checkerResult audit
        diagnostic report)

theorem ay_vrc_diagnostic_exit_no_claim
    (unknown parseError checkerReject archiveMismatch audit diagnostic : Prop) :
    (unknown -> audit) ->
    (unknown -> diagnostic) ->
    (parseError -> audit) ->
    (parseError -> diagnostic) ->
    (checkerReject -> audit) ->
    (checkerReject -> diagnostic) ->
    (archiveMismatch -> audit) ->
    (archiveMismatch -> diagnostic) ->
    AyVRCDiagnosticExit unknown parseError checkerReject archiveMismatch ->
    AyVRCDisj
      (AyVRCNoClaim unknown audit diagnostic)
      (AyVRCDisj
        (AyVRCNoClaim parseError audit diagnostic)
        (AyVRCDisj
          (AyVRCNoClaim checkerReject audit diagnostic)
          (AyVRCNoClaim archiveMismatch audit diagnostic))) :=
  fun unknownAudit unknownDiag parseAudit parseDiag rejectAudit rejectDiag
      mismatchAudit mismatchDiag diagnosticExit result onUnknown onRest =>
    diagnosticExit result
      (fun unknownProof =>
        onUnknown
          (ay_vrc_no_claim_intro unknown audit diagnostic unknownProof
            (unknownAudit unknownProof) (unknownDiag unknownProof)))
      (fun rest1 =>
        rest1 result
          (fun parseProof =>
            onRest
              (ay_vrc_disj_left
                (AyVRCNoClaim parseError audit diagnostic)
                (AyVRCDisj
                  (AyVRCNoClaim checkerReject audit diagnostic)
                  (AyVRCNoClaim archiveMismatch audit diagnostic))
                (ay_vrc_no_claim_intro parseError audit diagnostic parseProof
                  (parseAudit parseProof) (parseDiag parseProof))))
          (fun rest2 =>
            rest2 result
              (fun rejectProof =>
                onRest
                  (ay_vrc_disj_right
                    (AyVRCNoClaim parseError audit diagnostic)
                    (AyVRCDisj
                      (AyVRCNoClaim checkerReject audit diagnostic)
                      (AyVRCNoClaim archiveMismatch audit diagnostic))
                    (ay_vrc_disj_left
                      (AyVRCNoClaim checkerReject audit diagnostic)
                      (AyVRCNoClaim archiveMismatch audit diagnostic)
                      (ay_vrc_no_claim_intro checkerReject audit diagnostic
                        rejectProof (rejectAudit rejectProof)
                        (rejectDiag rejectProof)))))
              (fun mismatchProof =>
                onRest
                  (ay_vrc_disj_right
                    (AyVRCNoClaim parseError audit diagnostic)
                    (AyVRCDisj
                      (AyVRCNoClaim checkerReject audit diagnostic)
                      (AyVRCNoClaim archiveMismatch audit diagnostic))
                    (ay_vrc_disj_right
                      (AyVRCNoClaim checkerReject audit diagnostic)
                      (AyVRCNoClaim archiveMismatch audit diagnostic)
                      (ay_vrc_no_claim_intro archiveMismatch audit diagnostic
                        mismatchProof (mismatchAudit mismatchProof)
                        (mismatchDiag mismatchProof)))))))

theorem ay_vrc_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVRCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVRCModel solver internalAssignment ->
    AyVRCVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vrc_model_intro original visibleAssignment
      (ay_vrc_equisat_backward original solver preprocess
        (ay_vrc_model_formula solver internalAssignment model))
      (decode (ay_vrc_model_assignment solver internalAssignment model))

theorem ay_vrc_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVRCPreprocessArtifact original solver ->
    AyVRCUnsat solver ->
    AyVRCUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vrc_equisat_forward original solver preprocess originalProof)

theorem ay_vrc_replay_unsat_solver
    (solver stream finalClause : Prop) :
    AyVRCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVRCUnsat solver :=
  fun replay closeFinal streamProof solverProof =>
    closeFinal (replay streamProof solverProof)

theorem ay_vrc_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVRCPreprocessArtifact original solver ->
    AyVRCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVRCUnsat original :=
  fun preprocess replay closeFinal streamProof =>
    ay_vrc_preprocess_unsat_reconstruct original solver preprocess
      (ay_vrc_replay_unsat_solver solver stream finalClause replay
        closeFinal streamProof)

theorem ay_vrc_sat_report_sound
    (acceptedSat artifacts satBranch audit diagnostic original solver
      internalAssignment visibleAssignment : Prop) :
    AyVRCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVRCModel solver internalAssignment) ->
    AyVRCReport acceptedSat artifacts satBranch audit diagnostic ->
    AyVRCVisibleSAT original visibleAssignment :=
  fun preprocess decode accept report =>
    ay_vrc_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vrc_report_checker acceptedSat artifacts satBranch audit
          diagnostic report))

theorem ay_vrc_unsat_report_sound
    (acceptedUnsat artifacts unsatBranch audit diagnostic original solver
      stream finalClause : Prop) :
    AyVRCPreprocessArtifact original solver ->
    AyVRCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVRCReport acceptedUnsat artifacts unsatBranch audit diagnostic ->
    AyVRCUnsat original :=
  fun preprocess replay closeFinal accept report =>
    ay_vrc_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vrc_report_checker acceptedUnsat artifacts unsatBranch audit
          diagnostic report))

theorem ay_vrc_accepted_report_outcome
    (satReport unsatReport publicSat publicUnsat : Prop) :
    (satReport -> publicSat) ->
    (unsatReport -> publicUnsat) ->
    AyVRCOutcome satReport unsatReport ->
    AyVRCOutcome publicSat publicUnsat :=
  fun satSound unsatSound outcome result onSat onUnsat =>
    outcome result
      (fun satProof => onSat (satSound satProof))
      (fun unsatProof => onUnsat (unsatSound unsatProof))

theorem ay_vrc_report_public_result
    (satReport unsatReport diagnosticReport publicSat publicUnsat noClaim :
      Prop) :
    (satReport -> publicSat) ->
    (unsatReport -> publicUnsat) ->
    (diagnosticReport -> noClaim) ->
    AyVRCDisj satReport (AyVRCDisj unsatReport diagnosticReport) ->
    AyVRCPublicResult publicSat publicUnsat noClaim :=
  fun satSound unsatSound diagnosticSound report result onSat onRest =>
    report result
      (fun satProof => onSat (satSound satProof))
      (fun rest =>
        rest result
          (fun unsatProof =>
            onRest
              (ay_vrc_disj_left publicUnsat noClaim
                (unsatSound unsatProof)))
          (fun diagnosticProof =>
            onRest
              (ay_vrc_disj_right publicUnsat noClaim
                (diagnosticSound diagnosticProof))))

theorem ay_vrc_no_claim_public_result
    (satFact unsatFact exitCode audit diagnostic : Prop) :
    AyVRCNoClaim exitCode audit diagnostic ->
    AyVRCPublicResult satFact unsatFact
      (AyVRCNoClaim exitCode audit diagnostic) :=
  fun noClaim =>
    ay_vrc_disj_right satFact
      (AyVRCDisj unsatFact (AyVRCNoClaim exitCode audit diagnostic))
      (ay_vrc_disj_right unsatFact
        (AyVRCNoClaim exitCode audit diagnostic)
        noClaim)
