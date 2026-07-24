-- SAT-COMP validator audit-log contract core.
--
-- Audit logs are modeled as append-only Church records.  Accepted SAT/UNSAT
-- entries expose the same semantic facts as reports.  Appending diagnostic
-- entries preserves prior accepted soundness and adds only no-claim evidence.

def AyALCConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyALCDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyALCEquisat (before after : Prop) : Prop :=
  AyALCConj (before -> after) (after -> before)

def AyALCOutcome (sat unsat : Prop) : Prop :=
  AyALCDisj sat unsat

def AyALCPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyALCDisj satFact (AyALCDisj unsatFact noClaim)

def AyALCArtifacts (certId archiveKey : Prop) : Prop :=
  AyALCConj certId archiveKey

def AyALCReportEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyALCConj exitCode
    (AyALCConj artifacts
      (AyALCConj checkerDecision
        (AyALCConj auditDigest diagnostic)))

def AyALCAuditLog (entries tailDigest : Prop) : Prop :=
  AyALCConj entries tailDigest

def AyALCAppend (oldLog entry newLog : Prop) : Prop :=
  AyALCConj oldLog (AyALCConj entry newLog)

def AyALCNoClaim (exitCode auditDigest diagnostic : Prop) : Prop :=
  AyALCConj exitCode (AyALCConj auditDigest diagnostic)

def AyALCModel (formula assignment : Prop) : Prop :=
  AyALCConj formula assignment

def AyALCUnsat (formula : Prop) : Prop :=
  formula -> False

def AyALCVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyALCModel original visibleAssignment

def AyALCPreprocessArtifact (original solver : Prop) : Prop :=
  AyALCEquisat original solver

def AyALCReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

def AyALCSatChecker (branch visibleSat : Prop) : Prop :=
  branch -> visibleSat

def AyALCUnsatChecker (branch publicUnsat : Prop) : Prop :=
  branch -> publicUnsat

theorem ay_alc_conj_intro (left right : Prop) :
    left -> right -> AyALCConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_alc_conj_left (left right : Prop) :
    AyALCConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_alc_conj_right (left right : Prop) :
    AyALCConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_alc_disj_left (left right : Prop) :
    left -> AyALCDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_alc_disj_right (left right : Prop) :
    right -> AyALCDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_alc_equisat_forward (before after : Prop) :
    AyALCEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_alc_equisat_backward (before after : Prop) :
    AyALCEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_alc_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyALCModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_alc_conj_intro formula assignment formulaProof assignmentProof

theorem ay_alc_model_formula (formula assignment : Prop) :
    AyALCModel formula assignment -> formula :=
  fun model => ay_alc_conj_left formula assignment model

theorem ay_alc_model_assignment (formula assignment : Prop) :
    AyALCModel formula assignment -> assignment :=
  fun model => ay_alc_conj_right formula assignment model

theorem ay_alc_artifacts_intro (certId archiveKey : Prop) :
    certId -> archiveKey -> AyALCArtifacts certId archiveKey :=
  ay_alc_conj_intro certId archiveKey

theorem ay_alc_artifacts_cert (certId archiveKey : Prop) :
    AyALCArtifacts certId archiveKey -> certId :=
  ay_alc_conj_left certId archiveKey

theorem ay_alc_artifacts_archive (certId archiveKey : Prop) :
    AyALCArtifacts certId archiveKey -> archiveKey :=
  ay_alc_conj_right certId archiveKey

theorem ay_alc_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyALCReportEntry exitCode artifacts checkerDecision auditDigest
      diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_alc_conj_intro exitCode
      (AyALCConj artifacts
        (AyALCConj checkerDecision (AyALCConj auditDigest diagnostic)))
      exitProof
      (ay_alc_conj_intro artifacts
        (AyALCConj checkerDecision (AyALCConj auditDigest diagnostic))
        artifactsProof
        (ay_alc_conj_intro checkerDecision
          (AyALCConj auditDigest diagnostic)
          checkerProof
          (ay_alc_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_alc_entry_exit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyALCReportEntry exitCode artifacts checkerDecision auditDigest
      diagnostic ->
    exitCode :=
  fun entry =>
    ay_alc_conj_left exitCode
      (AyALCConj artifacts
        (AyALCConj checkerDecision (AyALCConj auditDigest diagnostic)))
      entry

theorem ay_alc_entry_artifacts
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyALCReportEntry exitCode artifacts checkerDecision auditDigest
      diagnostic ->
    artifacts :=
  fun entry =>
    ay_alc_conj_right exitCode
      (AyALCConj artifacts
        (AyALCConj checkerDecision (AyALCConj auditDigest diagnostic)))
      entry artifacts (fun artifactsProof _tail => artifactsProof)

theorem ay_alc_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyALCReportEntry exitCode artifacts checkerDecision auditDigest
      diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_alc_conj_right exitCode
      (AyALCConj artifacts
        (AyALCConj checkerDecision (AyALCConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision
          (fun checkerProof _auditTail => checkerProof))

theorem ay_alc_entry_audit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyALCReportEntry exitCode artifacts checkerDecision auditDigest
      diagnostic ->
    auditDigest :=
  fun entry =>
    ay_alc_conj_right exitCode
      (AyALCConj artifacts
        (AyALCConj checkerDecision (AyALCConj auditDigest diagnostic)))
      entry auditDigest
      (fun _artifactsProof tail =>
        tail auditDigest
          (fun _checkerProof auditTail =>
            auditTail auditDigest
              (fun auditProof _diagnosticProof => auditProof)))

theorem ay_alc_entry_diagnostic
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyALCReportEntry exitCode artifacts checkerDecision auditDigest
      diagnostic ->
    diagnostic :=
  fun entry =>
    ay_alc_conj_right exitCode
      (AyALCConj artifacts
        (AyALCConj checkerDecision (AyALCConj auditDigest diagnostic)))
      entry diagnostic
      (fun _artifactsProof tail =>
        tail diagnostic
          (fun _checkerProof auditTail =>
            auditTail diagnostic
              (fun _auditProof diagnosticProof => diagnosticProof)))

theorem ay_alc_log_intro (entries tailDigest : Prop) :
    entries -> tailDigest -> AyALCAuditLog entries tailDigest :=
  ay_alc_conj_intro entries tailDigest

theorem ay_alc_log_entries (entries tailDigest : Prop) :
    AyALCAuditLog entries tailDigest -> entries :=
  ay_alc_conj_left entries tailDigest

theorem ay_alc_log_tail_digest (entries tailDigest : Prop) :
    AyALCAuditLog entries tailDigest -> tailDigest :=
  ay_alc_conj_right entries tailDigest

theorem ay_alc_append_intro (oldLog entry newLog : Prop) :
    oldLog -> entry -> newLog -> AyALCAppend oldLog entry newLog :=
  fun oldProof entryProof newProof =>
    ay_alc_conj_intro oldLog (AyALCConj entry newLog)
      oldProof
      (ay_alc_conj_intro entry newLog entryProof newProof)

theorem ay_alc_append_old (oldLog entry newLog : Prop) :
    AyALCAppend oldLog entry newLog -> oldLog :=
  fun append =>
    ay_alc_conj_left oldLog (AyALCConj entry newLog) append

theorem ay_alc_append_entry (oldLog entry newLog : Prop) :
    AyALCAppend oldLog entry newLog -> entry :=
  fun append =>
    ay_alc_conj_right oldLog (AyALCConj entry newLog) append
      entry (fun entryProof _newProof => entryProof)

theorem ay_alc_append_new (oldLog entry newLog : Prop) :
    AyALCAppend oldLog entry newLog -> newLog :=
  fun append =>
    ay_alc_conj_right oldLog (AyALCConj entry newLog) append
      newLog (fun _entryProof newProof => newProof)

theorem ay_alc_no_claim_intro (exitCode auditDigest diagnostic : Prop) :
    exitCode -> auditDigest -> diagnostic ->
    AyALCNoClaim exitCode auditDigest diagnostic :=
  fun exitProof auditProof diagnosticProof =>
    ay_alc_conj_intro exitCode (AyALCConj auditDigest diagnostic)
      exitProof
      (ay_alc_conj_intro auditDigest diagnostic auditProof diagnosticProof)

theorem ay_alc_no_claim_audit (exitCode auditDigest diagnostic : Prop) :
    AyALCNoClaim exitCode auditDigest diagnostic -> auditDigest :=
  fun noClaim =>
    ay_alc_conj_right exitCode (AyALCConj auditDigest diagnostic) noClaim
      auditDigest (fun auditProof _diagnosticProof => auditProof)

theorem ay_alc_no_claim_diagnostic (exitCode auditDigest diagnostic : Prop) :
    AyALCNoClaim exitCode auditDigest diagnostic -> diagnostic :=
  fun noClaim =>
    ay_alc_conj_right exitCode (AyALCConj auditDigest diagnostic) noClaim
      diagnostic (fun _auditProof diagnosticProof => diagnosticProof)

theorem ay_alc_diagnostic_entry_no_claim
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyALCReportEntry exitCode artifacts checkerDecision auditDigest
      diagnostic ->
    AyALCNoClaim exitCode auditDigest diagnostic :=
  fun entry =>
    ay_alc_no_claim_intro exitCode auditDigest diagnostic
      (ay_alc_entry_exit exitCode artifacts checkerDecision auditDigest
        diagnostic entry)
      (ay_alc_entry_audit exitCode artifacts checkerDecision auditDigest
        diagnostic entry)
      (ay_alc_entry_diagnostic exitCode artifacts checkerDecision auditDigest
        diagnostic entry)

theorem ay_alc_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyALCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyALCModel solver internalAssignment ->
    AyALCVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_alc_model_intro original visibleAssignment
      (ay_alc_equisat_backward original solver preprocess
        (ay_alc_model_formula solver internalAssignment model))
      (decode (ay_alc_model_assignment solver internalAssignment model))

theorem ay_alc_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyALCPreprocessArtifact original solver ->
    AyALCUnsat solver ->
    AyALCUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_alc_equisat_forward original solver preprocess originalProof)

theorem ay_alc_replay_unsat_solver
    (solver stream finalClause : Prop) :
    AyALCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyALCUnsat solver :=
  fun replay closeFinal streamProof solverProof =>
    closeFinal (replay streamProof solverProof)

theorem ay_alc_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyALCPreprocessArtifact original solver ->
    AyALCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyALCUnsat original :=
  fun preprocess replay closeFinal streamProof =>
    ay_alc_preprocess_unsat_reconstruct original solver preprocess
      (ay_alc_replay_unsat_solver solver stream finalClause replay
        closeFinal streamProof)

theorem ay_alc_sat_entry_sound
    (acceptedSat artifacts satBranch auditDigest diagnostic original solver
      internalAssignment visibleAssignment : Prop) :
    AyALCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyALCModel solver internalAssignment) ->
    AyALCReportEntry acceptedSat artifacts satBranch auditDigest diagnostic ->
    AyALCVisibleSAT original visibleAssignment :=
  fun preprocess decode accept entry =>
    ay_alc_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_alc_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic entry))

theorem ay_alc_unsat_entry_sound
    (acceptedUnsat artifacts unsatBranch auditDigest diagnostic original solver
      stream finalClause : Prop) :
    AyALCPreprocessArtifact original solver ->
    AyALCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyALCReportEntry acceptedUnsat artifacts unsatBranch auditDigest
      diagnostic ->
    AyALCUnsat original :=
  fun preprocess replay closeFinal accept entry =>
    ay_alc_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_alc_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic entry))

theorem ay_alc_append_preserves_sat_soundness
    (oldLog diagnosticEntry newLog satFact : Prop) :
    AyALCAppend oldLog diagnosticEntry newLog ->
    (oldLog -> satFact) ->
    newLog ->
    satFact :=
  fun _append oldSound _newProof =>
    oldSound (ay_alc_append_old oldLog diagnosticEntry newLog _append)

theorem ay_alc_append_preserves_unsat_soundness
    (oldLog diagnosticEntry newLog unsatFact : Prop) :
    AyALCAppend oldLog diagnosticEntry newLog ->
    (oldLog -> unsatFact) ->
    newLog ->
    unsatFact :=
  fun _append oldSound _newProof =>
    oldSound (ay_alc_append_old oldLog diagnosticEntry newLog _append)

theorem ay_alc_append_diagnostic_no_claim
    (oldLog diagnosticEntry newLog exitCode artifacts checkerDecision
      auditDigest diagnostic : Prop) :
    AyALCAppend oldLog diagnosticEntry newLog ->
    (diagnosticEntry ->
      AyALCReportEntry exitCode artifacts checkerDecision auditDigest
        diagnostic) ->
    AyALCNoClaim exitCode auditDigest diagnostic :=
  fun append decodeEntry =>
    ay_alc_diagnostic_entry_no_claim exitCode artifacts checkerDecision
      auditDigest diagnostic
      (decodeEntry
        (ay_alc_append_entry oldLog diagnosticEntry newLog append))

theorem ay_alc_append_public_result
    (oldLog diagnosticEntry newLog satFact unsatFact exitCode artifacts
      checkerDecision auditDigest diagnostic : Prop) :
    AyALCAppend oldLog diagnosticEntry newLog ->
    (oldLog -> AyALCPublicResult satFact unsatFact
      (AyALCNoClaim exitCode auditDigest diagnostic)) ->
    (diagnosticEntry ->
      AyALCReportEntry exitCode artifacts checkerDecision auditDigest
        diagnostic) ->
    AyALCPublicResult satFact unsatFact
      (AyALCNoClaim exitCode auditDigest diagnostic) :=
  fun append oldResult _decodeEntry =>
    oldResult (ay_alc_append_old oldLog diagnosticEntry newLog append)
