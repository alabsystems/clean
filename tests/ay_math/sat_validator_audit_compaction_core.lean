-- SAT-COMP validator audit-log compaction core.
--
-- Compaction keeps a compact summary of an append-only validator log while
-- preserving accepted SAT/UNSAT entries, diagnostic no-claim entries, and tail
-- digest agreement.

def AyACCConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyACCDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyACCEquisat (before after : Prop) : Prop :=
  AyACCConj (before -> after) (after -> before)

def AyACCOutcome (sat unsat : Prop) : Prop :=
  AyACCDisj sat unsat

def AyACCPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyACCDisj satFact (AyACCDisj unsatFact noClaim)

def AyACCArtifacts (certId archiveKey : Prop) : Prop :=
  AyACCConj certId archiveKey

def AyACCEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyACCConj exitCode
    (AyACCConj artifacts
      (AyACCConj checkerDecision
        (AyACCConj auditDigest diagnostic)))

def AyACCLog (entries tailDigest : Prop) : Prop :=
  AyACCConj entries tailDigest

def AyACCAppend (oldLog entry newLog : Prop) : Prop :=
  AyACCConj oldLog (AyACCConj entry newLog)

def AyACCCompactedSummary
    (acceptedSat acceptedUnsat diagnostics tailDigest : Prop) : Prop :=
  AyACCConj acceptedSat
    (AyACCConj acceptedUnsat (AyACCConj diagnostics tailDigest))

def AyACCTailAgreement (logTail summaryTail : Prop) : Prop :=
  AyACCConj logTail summaryTail

def AyACCCompaction (log summary tailAgreement : Prop) : Prop :=
  AyACCConj log (AyACCConj summary tailAgreement)

def AyACCNoClaim (exitCode auditDigest diagnostic : Prop) : Prop :=
  AyACCConj exitCode (AyACCConj auditDigest diagnostic)

def AyACCModel (formula assignment : Prop) : Prop :=
  AyACCConj formula assignment

def AyACCUnsat (formula : Prop) : Prop :=
  formula -> False

def AyACCVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyACCModel original visibleAssignment

def AyACCPreprocessArtifact (original solver : Prop) : Prop :=
  AyACCEquisat original solver

def AyACCReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_acc_conj_intro (left right : Prop) :
    left -> right -> AyACCConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_acc_conj_left (left right : Prop) :
    AyACCConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_acc_conj_right (left right : Prop) :
    AyACCConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_acc_disj_left (left right : Prop) :
    left -> AyACCDisj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_acc_disj_right (left right : Prop) :
    right -> AyACCDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_acc_equisat_forward (before after : Prop) :
    AyACCEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_acc_equisat_backward (before after : Prop) :
    AyACCEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_acc_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyACCModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_acc_conj_intro formula assignment formulaProof assignmentProof

theorem ay_acc_model_formula (formula assignment : Prop) :
    AyACCModel formula assignment -> formula :=
  fun model => ay_acc_conj_left formula assignment model

theorem ay_acc_model_assignment (formula assignment : Prop) :
    AyACCModel formula assignment -> assignment :=
  fun model => ay_acc_conj_right formula assignment model

theorem ay_acc_artifacts_intro (certId archiveKey : Prop) :
    certId -> archiveKey -> AyACCArtifacts certId archiveKey :=
  ay_acc_conj_intro certId archiveKey

theorem ay_acc_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyACCEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_acc_conj_intro exitCode
      (AyACCConj artifacts
        (AyACCConj checkerDecision (AyACCConj auditDigest diagnostic)))
      exitProof
      (ay_acc_conj_intro artifacts
        (AyACCConj checkerDecision (AyACCConj auditDigest diagnostic))
        artifactsProof
        (ay_acc_conj_intro checkerDecision
          (AyACCConj auditDigest diagnostic)
          checkerProof
          (ay_acc_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_acc_entry_exit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyACCEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    exitCode :=
  fun entry =>
    ay_acc_conj_left exitCode
      (AyACCConj artifacts
        (AyACCConj checkerDecision (AyACCConj auditDigest diagnostic)))
      entry

theorem ay_acc_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyACCEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_acc_conj_right exitCode
      (AyACCConj artifacts
        (AyACCConj checkerDecision (AyACCConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_acc_entry_audit
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyACCEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    auditDigest :=
  fun entry =>
    ay_acc_conj_right exitCode
      (AyACCConj artifacts
        (AyACCConj checkerDecision (AyACCConj auditDigest diagnostic)))
      entry auditDigest
      (fun _artifactsProof tail =>
        tail auditDigest
          (fun _checkerProof auditTail =>
            auditTail auditDigest
              (fun auditProof _diagnosticProof => auditProof)))

theorem ay_acc_entry_diagnostic
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyACCEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    diagnostic :=
  fun entry =>
    ay_acc_conj_right exitCode
      (AyACCConj artifacts
        (AyACCConj checkerDecision (AyACCConj auditDigest diagnostic)))
      entry diagnostic
      (fun _artifactsProof tail =>
        tail diagnostic
          (fun _checkerProof auditTail =>
            auditTail diagnostic
              (fun _auditProof diagnosticProof => diagnosticProof)))

theorem ay_acc_log_intro (entries tailDigest : Prop) :
    entries -> tailDigest -> AyACCLog entries tailDigest :=
  ay_acc_conj_intro entries tailDigest

theorem ay_acc_log_entries (entries tailDigest : Prop) :
    AyACCLog entries tailDigest -> entries :=
  ay_acc_conj_left entries tailDigest

theorem ay_acc_log_tail_digest (entries tailDigest : Prop) :
    AyACCLog entries tailDigest -> tailDigest :=
  ay_acc_conj_right entries tailDigest

theorem ay_acc_append_intro (oldLog entry newLog : Prop) :
    oldLog -> entry -> newLog -> AyACCAppend oldLog entry newLog :=
  fun oldProof entryProof newProof =>
    ay_acc_conj_intro oldLog (AyACCConj entry newLog)
      oldProof
      (ay_acc_conj_intro entry newLog entryProof newProof)

theorem ay_acc_append_old (oldLog entry newLog : Prop) :
    AyACCAppend oldLog entry newLog -> oldLog :=
  fun append => ay_acc_conj_left oldLog (AyACCConj entry newLog) append

theorem ay_acc_append_entry (oldLog entry newLog : Prop) :
    AyACCAppend oldLog entry newLog -> entry :=
  fun append =>
    ay_acc_conj_right oldLog (AyACCConj entry newLog) append
      entry (fun entryProof _newProof => entryProof)

theorem ay_acc_append_new (oldLog entry newLog : Prop) :
    AyACCAppend oldLog entry newLog -> newLog :=
  fun append =>
    ay_acc_conj_right oldLog (AyACCConj entry newLog) append
      newLog (fun _entryProof newProof => newProof)

theorem ay_acc_summary_intro
    (acceptedSat acceptedUnsat diagnostics tailDigest : Prop) :
    acceptedSat -> acceptedUnsat -> diagnostics -> tailDigest ->
    AyACCCompactedSummary acceptedSat acceptedUnsat diagnostics
      tailDigest :=
  fun satProof unsatProof diagnosticsProof tailProof =>
    ay_acc_conj_intro acceptedSat
      (AyACCConj acceptedUnsat (AyACCConj diagnostics tailDigest))
      satProof
      (ay_acc_conj_intro acceptedUnsat
        (AyACCConj diagnostics tailDigest)
        unsatProof
        (ay_acc_conj_intro diagnostics tailDigest diagnosticsProof
          tailProof))

theorem ay_acc_summary_sat
    (acceptedSat acceptedUnsat diagnostics tailDigest : Prop) :
    AyACCCompactedSummary acceptedSat acceptedUnsat diagnostics
      tailDigest ->
    acceptedSat :=
  fun summary =>
    ay_acc_conj_left acceptedSat
      (AyACCConj acceptedUnsat (AyACCConj diagnostics tailDigest))
      summary

theorem ay_acc_summary_unsat
    (acceptedSat acceptedUnsat diagnostics tailDigest : Prop) :
    AyACCCompactedSummary acceptedSat acceptedUnsat diagnostics
      tailDigest ->
    acceptedUnsat :=
  fun summary =>
    ay_acc_conj_right acceptedSat
      (AyACCConj acceptedUnsat (AyACCConj diagnostics tailDigest))
      summary acceptedUnsat
      (fun unsatProof _tail => unsatProof)

theorem ay_acc_summary_diagnostics
    (acceptedSat acceptedUnsat diagnostics tailDigest : Prop) :
    AyACCCompactedSummary acceptedSat acceptedUnsat diagnostics
      tailDigest ->
    diagnostics :=
  fun summary =>
    ay_acc_conj_right acceptedSat
      (AyACCConj acceptedUnsat (AyACCConj diagnostics tailDigest))
      summary diagnostics
      (fun _unsatProof tail =>
        tail diagnostics (fun diagnosticsProof _tailProof =>
          diagnosticsProof))

theorem ay_acc_summary_tail_digest
    (acceptedSat acceptedUnsat diagnostics tailDigest : Prop) :
    AyACCCompactedSummary acceptedSat acceptedUnsat diagnostics
      tailDigest ->
    tailDigest :=
  fun summary =>
    ay_acc_conj_right acceptedSat
      (AyACCConj acceptedUnsat (AyACCConj diagnostics tailDigest))
      summary tailDigest
      (fun _unsatProof tail =>
        tail tailDigest (fun _diagnosticsProof tailProof => tailProof))

theorem ay_acc_tail_agreement_intro (logTail summaryTail : Prop) :
    logTail -> summaryTail -> AyACCTailAgreement logTail summaryTail :=
  ay_acc_conj_intro logTail summaryTail

theorem ay_acc_tail_agreement_log (logTail summaryTail : Prop) :
    AyACCTailAgreement logTail summaryTail -> logTail :=
  ay_acc_conj_left logTail summaryTail

theorem ay_acc_tail_agreement_summary (logTail summaryTail : Prop) :
    AyACCTailAgreement logTail summaryTail -> summaryTail :=
  ay_acc_conj_right logTail summaryTail

theorem ay_acc_compaction_intro (log summary tailAgreement : Prop) :
    log -> summary -> tailAgreement ->
    AyACCCompaction log summary tailAgreement :=
  fun logProof summaryProof tailProof =>
    ay_acc_conj_intro log (AyACCConj summary tailAgreement)
      logProof
      (ay_acc_conj_intro summary tailAgreement summaryProof tailProof)

theorem ay_acc_compaction_log (log summary tailAgreement : Prop) :
    AyACCCompaction log summary tailAgreement -> log :=
  fun compaction =>
    ay_acc_conj_left log (AyACCConj summary tailAgreement) compaction

theorem ay_acc_compaction_summary (log summary tailAgreement : Prop) :
    AyACCCompaction log summary tailAgreement -> summary :=
  fun compaction =>
    ay_acc_conj_right log (AyACCConj summary tailAgreement) compaction
      summary (fun summaryProof _tailProof => summaryProof)

theorem ay_acc_compaction_tail_agreement
    (log summary tailAgreement : Prop) :
    AyACCCompaction log summary tailAgreement -> tailAgreement :=
  fun compaction =>
    ay_acc_conj_right log (AyACCConj summary tailAgreement) compaction
      tailAgreement (fun _summaryProof tailProof => tailProof)

theorem ay_acc_no_claim_intro (exitCode auditDigest diagnostic : Prop) :
    exitCode -> auditDigest -> diagnostic ->
    AyACCNoClaim exitCode auditDigest diagnostic :=
  fun exitProof auditProof diagnosticProof =>
    ay_acc_conj_intro exitCode (AyACCConj auditDigest diagnostic)
      exitProof
      (ay_acc_conj_intro auditDigest diagnostic auditProof diagnosticProof)

theorem ay_acc_diagnostic_entry_no_claim
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyACCEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    AyACCNoClaim exitCode auditDigest diagnostic :=
  fun entry =>
    ay_acc_no_claim_intro exitCode auditDigest diagnostic
      (ay_acc_entry_exit exitCode artifacts checkerDecision auditDigest
        diagnostic entry)
      (ay_acc_entry_audit exitCode artifacts checkerDecision auditDigest
        diagnostic entry)
      (ay_acc_entry_diagnostic exitCode artifacts checkerDecision auditDigest
        diagnostic entry)

theorem ay_acc_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyACCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyACCModel solver internalAssignment ->
    AyACCVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_acc_model_intro original visibleAssignment
      (ay_acc_equisat_backward original solver preprocess
        (ay_acc_model_formula solver internalAssignment model))
      (decode (ay_acc_model_assignment solver internalAssignment model))

theorem ay_acc_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyACCPreprocessArtifact original solver ->
    AyACCUnsat solver ->
    AyACCUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_acc_equisat_forward original solver preprocess originalProof)

theorem ay_acc_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyACCPreprocessArtifact original solver ->
    AyACCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyACCUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_acc_equisat_forward original solver preprocess originalProof))

theorem ay_acc_sat_entry_sound
    (acceptedSat artifacts satBranch auditDigest diagnostic original solver
      internalAssignment visibleAssignment : Prop) :
    AyACCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyACCModel solver internalAssignment) ->
    AyACCEntry acceptedSat artifacts satBranch auditDigest diagnostic ->
    AyACCVisibleSAT original visibleAssignment :=
  fun preprocess decode accept entry =>
    ay_acc_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_acc_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic entry))

theorem ay_acc_unsat_entry_sound
    (acceptedUnsat artifacts unsatBranch auditDigest diagnostic original solver
      stream finalClause : Prop) :
    AyACCPreprocessArtifact original solver ->
    AyACCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyACCEntry acceptedUnsat artifacts unsatBranch auditDigest diagnostic ->
    AyACCUnsat original :=
  fun preprocess replay closeFinal accept entry =>
    ay_acc_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_acc_entry_checker acceptedUnsat artifacts unsatBranch auditDigest
          diagnostic entry))

theorem ay_acc_compaction_preserves_sat_soundness
    (log summary tailAgreement satFact : Prop) :
    AyACCCompaction log summary tailAgreement ->
    (log -> satFact) ->
    summary ->
    satFact :=
  fun compaction logSound _summaryProof =>
    logSound (ay_acc_compaction_log log summary tailAgreement compaction)

theorem ay_acc_compaction_preserves_unsat_soundness
    (log summary tailAgreement unsatFact : Prop) :
    AyACCCompaction log summary tailAgreement ->
    (log -> unsatFact) ->
    summary ->
    unsatFact :=
  fun compaction logSound _summaryProof =>
    logSound (ay_acc_compaction_log log summary tailAgreement compaction)

theorem ay_acc_compacted_summary_sat_soundness
    (acceptedSat acceptedUnsat diagnostics tailDigest satFact : Prop) :
    (acceptedSat -> satFact) ->
    AyACCCompactedSummary acceptedSat acceptedUnsat diagnostics
      tailDigest ->
    satFact :=
  fun satSound summary =>
    satSound
      (ay_acc_summary_sat acceptedSat acceptedUnsat diagnostics tailDigest
        summary)

theorem ay_acc_compacted_summary_unsat_soundness
    (acceptedSat acceptedUnsat diagnostics tailDigest unsatFact : Prop) :
    (acceptedUnsat -> unsatFact) ->
    AyACCCompactedSummary acceptedSat acceptedUnsat diagnostics
      tailDigest ->
    unsatFact :=
  fun unsatSound summary =>
    unsatSound
      (ay_acc_summary_unsat acceptedSat acceptedUnsat diagnostics tailDigest
        summary)

theorem ay_acc_compacted_diagnostic_no_claim
    (acceptedSat acceptedUnsat diagnostics tailDigest noClaim : Prop) :
    (diagnostics -> noClaim) ->
    AyACCCompactedSummary acceptedSat acceptedUnsat diagnostics
      tailDigest ->
    noClaim :=
  fun diagnosticsNoClaim summary =>
    diagnosticsNoClaim
      (ay_acc_summary_diagnostics acceptedSat acceptedUnsat diagnostics
        tailDigest summary)

theorem ay_acc_compaction_tail_digest_agrees
    (log summary logTail summaryTail : Prop) :
    AyACCCompaction log summary (AyACCTailAgreement logTail summaryTail) ->
    AyACCTailAgreement logTail summaryTail :=
  fun compaction =>
    ay_acc_compaction_tail_agreement log summary
      (AyACCTailAgreement logTail summaryTail) compaction

theorem ay_acc_compaction_public_result_preserved
    (log summary tailAgreement satFact unsatFact noClaim : Prop) :
    AyACCCompaction log summary tailAgreement ->
    (log -> AyACCPublicResult satFact unsatFact noClaim) ->
    summary ->
    AyACCPublicResult satFact unsatFact noClaim :=
  fun compaction logResult _summaryProof =>
    logResult (ay_acc_compaction_log log summary tailAgreement compaction)
