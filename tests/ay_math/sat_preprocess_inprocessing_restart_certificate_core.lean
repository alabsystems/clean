-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Inprocessing restart-epoch certificate soundness. The propositions stand for
-- restart epoch fingerprints, equisatisfiability witnesses, learned-clause
-- dependency preservation, model/proof reconstruction maps, digest membership,
-- checker replay, diagnostics, and public SAT/UNSAT outcomes.

def ay_pirc_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pirc_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pirc_Equisat (before : Prop) (after : Prop) :=
  ay_pirc_Conj (before -> after) (after -> before)

def ay_pirc_Sat (cnf : Prop) (model : Prop) :=
  ay_pirc_Conj cnf model

def ay_pirc_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pirc_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pirc_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pirc_FingerprintLineage
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop) :=
  ay_pirc_Conj lineageWitness
    (ay_pirc_IdMatch beforeFingerprint afterFingerprint)

def ay_pirc_DependencyPreservation
    (learnedDependencies : Prop) (preservedDependencies : Prop) :=
  ay_pirc_Conj learnedDependencies
    (learnedDependencies -> preservedDependencies)

def ay_pirc_ModelReconstruction
    (afterCnf : Prop) (beforeCnf : Prop)
    (afterModel : Prop) (beforeModel : Prop) :=
  ay_pirc_Sat afterCnf afterModel ->
    ay_pirc_Sat beforeCnf beforeModel

def ay_pirc_ProofReconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pirc_Replay afterCnf certificate conflict ->
    certificate -> beforeCnf -> conflict

def ay_pirc_DigestMembership (epochDigest : Prop) (runDigest : Prop) :=
  ay_pirc_Conj epochDigest runDigest

def ay_pirc_CheckerReplay (epochCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pirc_Conj epochCertificate checkerAccepted

def ay_pirc_RestartEpochCertificate
    (beforeCnf : Prop) (afterCnf : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (learnedDependencies : Prop) (preservedDependencies : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (epochDigest : Prop) (runDigest : Prop)
    (epochCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pirc_Conj
    (ay_pirc_FingerprintLineage
      beforeFingerprint afterFingerprint lineageWitness)
    (ay_pirc_Conj
      (ay_pirc_Equisat beforeCnf afterCnf)
      (ay_pirc_Conj
        (ay_pirc_DependencyPreservation
          learnedDependencies preservedDependencies)
        (ay_pirc_Conj
          (ay_pirc_ModelReconstruction
            afterCnf beforeCnf afterModel beforeModel)
          (ay_pirc_Conj
            (ay_pirc_ProofReconstruction
              beforeCnf afterCnf certificate conflict)
            (ay_pirc_Conj
              (ay_pirc_DigestMembership epochDigest runDigest)
              (ay_pirc_CheckerReplay
                epochCertificate checkerAccepted))))))

def ay_pirc_AcceptedEpochLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (beforeCnf : Prop) (afterCnf : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (learnedDependencies : Prop) (preservedDependencies : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (epochDigest : Prop) (runDigest : Prop)
    (epochCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pirc_Conj previousLog
    (ay_pirc_Conj
      (ay_pirc_RestartEpochCertificate
        beforeCnf afterCnf beforeFingerprint afterFingerprint
        lineageWitness learnedDependencies preservedDependencies
        afterModel beforeModel certificate conflict epochDigest runDigest
        epochCertificate checkerAccepted)
      nextLog)

def ay_pirc_EpochFailure
    (staleFingerprint : Prop) (missingDependencyPreservation : Prop)
    (brokenReconstruction : Prop) (replayRejected : Prop) :=
  ay_pirc_Disj staleFingerprint
    (ay_pirc_Disj missingDependencyPreservation
      (ay_pirc_Disj brokenReconstruction replayRejected))

def ay_pirc_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pirc_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pirc_Conj currentCnf recompute

def ay_pirc_DiagnosticEpochLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleFingerprint : Prop) (missingDependencyPreservation : Prop)
    (brokenReconstruction : Prop) (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pirc_Conj previousLog
    (ay_pirc_Conj
      (ay_pirc_Conj
        (ay_pirc_EpochFailure
          staleFingerprint missingDependencyPreservation
          brokenReconstruction replayRejected)
        (ay_pirc_Conj
          (ay_pirc_RecomputeObligation currentCnf recompute)
          (ay_pirc_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pirc_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pirc_Conj exitCode claim

def ay_pirc_PublicResult
    (beforeCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pirc_Disj
    (ay_pirc_ExitCodeSound exitCode (ay_pirc_Sat beforeCnf model))
    (ay_pirc_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))

theorem ay_pirc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pirc_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pirc_conj_left
    (left : Prop) (right : Prop) :
    ay_pirc_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pirc_conj_right
    (left : Prop) (right : Prop) :
    ay_pirc_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pirc_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pirc_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pirc_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pirc_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pirc_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pirc_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pirc_conj_left (before -> after) (after -> before) eq

theorem ay_pirc_epoch_equisat
    (beforeCnf : Prop) (afterCnf : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (learnedDependencies : Prop) (preservedDependencies : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (epochDigest : Prop) (runDigest : Prop)
    (epochCertificate : Prop) (checkerAccepted : Prop) :
    ay_pirc_RestartEpochCertificate
      beforeCnf afterCnf beforeFingerprint afterFingerprint
      lineageWitness learnedDependencies preservedDependencies
      afterModel beforeModel certificate conflict epochDigest runDigest
      epochCertificate checkerAccepted ->
    ay_pirc_Equisat beforeCnf afterCnf := by
  intro epoch
  exact ay_pirc_conj_left
    (ay_pirc_Equisat beforeCnf afterCnf)
    (ay_pirc_Conj
      (ay_pirc_DependencyPreservation
        learnedDependencies preservedDependencies)
      (ay_pirc_Conj
        (ay_pirc_ModelReconstruction afterCnf beforeCnf afterModel beforeModel)
        (ay_pirc_Conj
          (ay_pirc_ProofReconstruction beforeCnf afterCnf certificate conflict)
          (ay_pirc_Conj
            (ay_pirc_DigestMembership epochDigest runDigest)
            (ay_pirc_CheckerReplay epochCertificate checkerAccepted)))))
    (ay_pirc_conj_right
      (ay_pirc_FingerprintLineage
        beforeFingerprint afterFingerprint lineageWitness)
      (ay_pirc_Conj
        (ay_pirc_Equisat beforeCnf afterCnf)
        (ay_pirc_Conj
          (ay_pirc_DependencyPreservation
            learnedDependencies preservedDependencies)
          (ay_pirc_Conj
            (ay_pirc_ModelReconstruction
              afterCnf beforeCnf afterModel beforeModel)
            (ay_pirc_Conj
              (ay_pirc_ProofReconstruction
                beforeCnf afterCnf certificate conflict)
              (ay_pirc_Conj
                (ay_pirc_DigestMembership epochDigest runDigest)
                (ay_pirc_CheckerReplay
                  epochCertificate checkerAccepted))))))
      epoch)

theorem ay_pirc_epoch_dependency
    (beforeCnf : Prop) (afterCnf : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (learnedDependencies : Prop) (preservedDependencies : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (epochDigest : Prop) (runDigest : Prop)
    (epochCertificate : Prop) (checkerAccepted : Prop) :
    ay_pirc_RestartEpochCertificate
      beforeCnf afterCnf beforeFingerprint afterFingerprint
      lineageWitness learnedDependencies preservedDependencies
      afterModel beforeModel certificate conflict epochDigest runDigest
      epochCertificate checkerAccepted ->
    ay_pirc_DependencyPreservation
      learnedDependencies preservedDependencies := by
  intro epoch
  exact ay_pirc_conj_left
    (ay_pirc_DependencyPreservation
      learnedDependencies preservedDependencies)
    (ay_pirc_Conj
      (ay_pirc_ModelReconstruction afterCnf beforeCnf afterModel beforeModel)
      (ay_pirc_Conj
        (ay_pirc_ProofReconstruction beforeCnf afterCnf certificate conflict)
        (ay_pirc_Conj
          (ay_pirc_DigestMembership epochDigest runDigest)
          (ay_pirc_CheckerReplay epochCertificate checkerAccepted))))
    (ay_pirc_conj_right
      (ay_pirc_Equisat beforeCnf afterCnf)
      (ay_pirc_Conj
        (ay_pirc_DependencyPreservation
          learnedDependencies preservedDependencies)
        (ay_pirc_Conj
          (ay_pirc_ModelReconstruction afterCnf beforeCnf afterModel beforeModel)
          (ay_pirc_Conj
            (ay_pirc_ProofReconstruction beforeCnf afterCnf certificate conflict)
            (ay_pirc_Conj
              (ay_pirc_DigestMembership epochDigest runDigest)
              (ay_pirc_CheckerReplay epochCertificate checkerAccepted)))))
      (ay_pirc_conj_right
        (ay_pirc_FingerprintLineage
          beforeFingerprint afterFingerprint lineageWitness)
        (ay_pirc_Conj
          (ay_pirc_Equisat beforeCnf afterCnf)
          (ay_pirc_Conj
            (ay_pirc_DependencyPreservation
              learnedDependencies preservedDependencies)
            (ay_pirc_Conj
              (ay_pirc_ModelReconstruction
                afterCnf beforeCnf afterModel beforeModel)
              (ay_pirc_Conj
                (ay_pirc_ProofReconstruction
                  beforeCnf afterCnf certificate conflict)
                (ay_pirc_Conj
                  (ay_pirc_DigestMembership epochDigest runDigest)
                  (ay_pirc_CheckerReplay
                    epochCertificate checkerAccepted))))))
        epoch))

theorem ay_pirc_epoch_model_reconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (learnedDependencies : Prop) (preservedDependencies : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (epochDigest : Prop) (runDigest : Prop)
    (epochCertificate : Prop) (checkerAccepted : Prop) :
    ay_pirc_RestartEpochCertificate
      beforeCnf afterCnf beforeFingerprint afterFingerprint
      lineageWitness learnedDependencies preservedDependencies
      afterModel beforeModel certificate conflict epochDigest runDigest
      epochCertificate checkerAccepted ->
    ay_pirc_ModelReconstruction afterCnf beforeCnf afterModel beforeModel := by
  intro epoch
  exact epoch
    (ay_pirc_ModelReconstruction afterCnf beforeCnf afterModel beforeModel)
    (fun _lineage rest1 =>
      rest1
        (ay_pirc_ModelReconstruction afterCnf beforeCnf afterModel beforeModel)
        (fun _eq rest2 =>
          rest2
            (ay_pirc_ModelReconstruction
              afterCnf beforeCnf afterModel beforeModel)
            (fun _dep rest3 =>
              rest3
                (ay_pirc_ModelReconstruction
                  afterCnf beforeCnf afterModel beforeModel)
                (fun model _tail => model))))

theorem ay_pirc_epoch_proof_reconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (learnedDependencies : Prop) (preservedDependencies : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (epochDigest : Prop) (runDigest : Prop)
    (epochCertificate : Prop) (checkerAccepted : Prop) :
    ay_pirc_RestartEpochCertificate
      beforeCnf afterCnf beforeFingerprint afterFingerprint
      lineageWitness learnedDependencies preservedDependencies
      afterModel beforeModel certificate conflict epochDigest runDigest
      epochCertificate checkerAccepted ->
    ay_pirc_ProofReconstruction beforeCnf afterCnf certificate conflict := by
  intro epoch
  exact epoch
    (ay_pirc_ProofReconstruction beforeCnf afterCnf certificate conflict)
    (fun _lineage rest1 =>
      rest1
        (ay_pirc_ProofReconstruction beforeCnf afterCnf certificate conflict)
        (fun _eq rest2 =>
          rest2
            (ay_pirc_ProofReconstruction beforeCnf afterCnf certificate conflict)
            (fun _dep rest3 =>
              rest3
                (ay_pirc_ProofReconstruction
                  beforeCnf afterCnf certificate conflict)
                (fun _model rest4 =>
                  rest4
                    (ay_pirc_ProofReconstruction
                      beforeCnf afterCnf certificate conflict)
                    (fun proof _tail => proof)))))

theorem ay_pirc_log_epoch
    (previousLog : Prop) (nextLog : Prop)
    (beforeCnf : Prop) (afterCnf : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (learnedDependencies : Prop) (preservedDependencies : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (epochDigest : Prop) (runDigest : Prop)
    (epochCertificate : Prop) (checkerAccepted : Prop) :
    ay_pirc_AcceptedEpochLogEntry
      previousLog nextLog beforeCnf afterCnf beforeFingerprint
      afterFingerprint lineageWitness learnedDependencies
      preservedDependencies afterModel beforeModel certificate conflict
      epochDigest runDigest epochCertificate checkerAccepted ->
    ay_pirc_RestartEpochCertificate
      beforeCnf afterCnf beforeFingerprint afterFingerprint
      lineageWitness learnedDependencies preservedDependencies
      afterModel beforeModel certificate conflict epochDigest runDigest
      epochCertificate checkerAccepted := by
  intro log_entry
  exact ay_pirc_conj_left
    (ay_pirc_RestartEpochCertificate
      beforeCnf afterCnf beforeFingerprint afterFingerprint
      lineageWitness learnedDependencies preservedDependencies
      afterModel beforeModel certificate conflict epochDigest runDigest
      epochCertificate checkerAccepted)
    nextLog
    (ay_pirc_conj_right previousLog
      (ay_pirc_Conj
        (ay_pirc_RestartEpochCertificate
          beforeCnf afterCnf beforeFingerprint afterFingerprint
          lineageWitness learnedDependencies preservedDependencies
          afterModel beforeModel certificate conflict epochDigest runDigest
          epochCertificate checkerAccepted)
        nextLog)
      log_entry)

theorem ay_pirc_public_sat
    (previousLog : Prop) (nextLog : Prop)
    (beforeCnf : Prop) (afterCnf : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (learnedDependencies : Prop) (preservedDependencies : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (epochDigest : Prop) (runDigest : Prop)
    (epochCertificate : Prop) (checkerAccepted : Prop)
    (exitCode : Prop) :
    ay_pirc_AcceptedEpochLogEntry
      previousLog nextLog beforeCnf afterCnf beforeFingerprint
      afterFingerprint lineageWitness learnedDependencies
      preservedDependencies afterModel beforeModel certificate conflict
      epochDigest runDigest epochCertificate checkerAccepted ->
    ay_pirc_Sat afterCnf afterModel ->
    exitCode ->
    ay_pirc_PublicResult beforeCnf beforeModel certificate conflict exitCode := by
  intro log_entry sat hexit
  exact ay_pirc_disj_left
    (ay_pirc_ExitCodeSound exitCode (ay_pirc_Sat beforeCnf beforeModel))
    (ay_pirc_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))
    (ay_pirc_conj_intro exitCode (ay_pirc_Sat beforeCnf beforeModel)
      hexit
      (ay_pirc_epoch_model_reconstruction beforeCnf afterCnf
        beforeFingerprint afterFingerprint lineageWitness learnedDependencies
        preservedDependencies afterModel beforeModel certificate conflict
        epochDigest runDigest epochCertificate checkerAccepted
        (ay_pirc_log_epoch previousLog nextLog beforeCnf afterCnf
          beforeFingerprint afterFingerprint lineageWitness learnedDependencies
          preservedDependencies afterModel beforeModel certificate conflict
          epochDigest runDigest epochCertificate checkerAccepted log_entry)
        sat))

theorem ay_pirc_public_unsat
    (previousLog : Prop) (nextLog : Prop)
    (beforeCnf : Prop) (afterCnf : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (learnedDependencies : Prop) (preservedDependencies : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (epochDigest : Prop) (runDigest : Prop)
    (epochCertificate : Prop) (checkerAccepted : Prop)
    (exitCode : Prop) :
    ay_pirc_AcceptedEpochLogEntry
      previousLog nextLog beforeCnf afterCnf beforeFingerprint
      afterFingerprint lineageWitness learnedDependencies
      preservedDependencies afterModel beforeModel certificate conflict
      epochDigest runDigest epochCertificate checkerAccepted ->
    ay_pirc_Replay afterCnf certificate conflict ->
    exitCode ->
    ay_pirc_PublicResult beforeCnf beforeModel certificate conflict exitCode := by
  intro log_entry replay hexit
  exact ay_pirc_disj_right
    (ay_pirc_ExitCodeSound exitCode (ay_pirc_Sat beforeCnf beforeModel))
    (ay_pirc_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))
    (ay_pirc_conj_intro exitCode
      (certificate -> beforeCnf -> conflict)
      hexit
      (ay_pirc_epoch_proof_reconstruction beforeCnf afterCnf
        beforeFingerprint afterFingerprint lineageWitness learnedDependencies
        preservedDependencies afterModel beforeModel certificate conflict
        epochDigest runDigest epochCertificate checkerAccepted
        (ay_pirc_log_epoch previousLog nextLog beforeCnf afterCnf
          beforeFingerprint afterFingerprint lineageWitness learnedDependencies
          preservedDependencies afterModel beforeModel certificate conflict
          epochDigest runDigest epochCertificate checkerAccepted log_entry)
        replay))

theorem ay_pirc_failure_stale_fingerprint
    (staleFingerprint : Prop) (missingDependencyPreservation : Prop)
    (brokenReconstruction : Prop) (replayRejected : Prop) :
    staleFingerprint ->
    ay_pirc_EpochFailure
      staleFingerprint missingDependencyPreservation
      brokenReconstruction replayRejected := by
  intro hfailure
  exact ay_pirc_disj_left staleFingerprint
    (ay_pirc_Disj missingDependencyPreservation
      (ay_pirc_Disj brokenReconstruction replayRejected))
    hfailure

theorem ay_pirc_failure_missing_dependency
    (staleFingerprint : Prop) (missingDependencyPreservation : Prop)
    (brokenReconstruction : Prop) (replayRejected : Prop) :
    missingDependencyPreservation ->
    ay_pirc_EpochFailure
      staleFingerprint missingDependencyPreservation
      brokenReconstruction replayRejected := by
  intro hfailure
  exact ay_pirc_disj_right staleFingerprint
    (ay_pirc_Disj missingDependencyPreservation
      (ay_pirc_Disj brokenReconstruction replayRejected))
    (ay_pirc_disj_left missingDependencyPreservation
      (ay_pirc_Disj brokenReconstruction replayRejected)
      hfailure)

theorem ay_pirc_failure_broken_reconstruction
    (staleFingerprint : Prop) (missingDependencyPreservation : Prop)
    (brokenReconstruction : Prop) (replayRejected : Prop) :
    brokenReconstruction ->
    ay_pirc_EpochFailure
      staleFingerprint missingDependencyPreservation
      brokenReconstruction replayRejected := by
  intro hfailure
  exact ay_pirc_disj_right staleFingerprint
    (ay_pirc_Disj missingDependencyPreservation
      (ay_pirc_Disj brokenReconstruction replayRejected))
    (ay_pirc_disj_right missingDependencyPreservation
      (ay_pirc_Disj brokenReconstruction replayRejected)
      (ay_pirc_disj_left brokenReconstruction replayRejected hfailure))

theorem ay_pirc_failure_replay_rejected
    (staleFingerprint : Prop) (missingDependencyPreservation : Prop)
    (brokenReconstruction : Prop) (replayRejected : Prop) :
    replayRejected ->
    ay_pirc_EpochFailure
      staleFingerprint missingDependencyPreservation
      brokenReconstruction replayRejected := by
  intro hfailure
  exact ay_pirc_disj_right staleFingerprint
    (ay_pirc_Disj missingDependencyPreservation
      (ay_pirc_Disj brokenReconstruction replayRejected))
    (ay_pirc_disj_right missingDependencyPreservation
      (ay_pirc_Disj brokenReconstruction replayRejected)
      (ay_pirc_disj_right brokenReconstruction replayRejected hfailure))

theorem ay_pirc_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleFingerprint : Prop) (missingDependencyPreservation : Prop)
    (brokenReconstruction : Prop) (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pirc_DiagnosticEpochLogEntry
      previousLog nextLog currentCnf staleFingerprint
      missingDependencyPreservation brokenReconstruction replayRejected
      recompute diagnostic ->
    ay_pirc_EpochFailure
      staleFingerprint missingDependencyPreservation
      brokenReconstruction replayRejected := by
  intro log_entry
  exact ay_pirc_conj_left
    (ay_pirc_EpochFailure
      staleFingerprint missingDependencyPreservation
      brokenReconstruction replayRejected)
    (ay_pirc_Conj
      (ay_pirc_RecomputeObligation currentCnf recompute)
      (ay_pirc_NoSemanticClaim diagnostic))
    (ay_pirc_conj_left
      (ay_pirc_Conj
        (ay_pirc_EpochFailure
          staleFingerprint missingDependencyPreservation
          brokenReconstruction replayRejected)
        (ay_pirc_Conj
          (ay_pirc_RecomputeObligation currentCnf recompute)
          (ay_pirc_NoSemanticClaim diagnostic)))
      nextLog
      (ay_pirc_conj_right previousLog
        (ay_pirc_Conj
          (ay_pirc_Conj
            (ay_pirc_EpochFailure
              staleFingerprint missingDependencyPreservation
              brokenReconstruction replayRejected)
            (ay_pirc_Conj
              (ay_pirc_RecomputeObligation currentCnf recompute)
              (ay_pirc_NoSemanticClaim diagnostic)))
          nextLog)
        log_entry))

theorem ay_pirc_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleFingerprint : Prop) (missingDependencyPreservation : Prop)
    (brokenReconstruction : Prop) (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pirc_DiagnosticEpochLogEntry
      previousLog nextLog currentCnf staleFingerprint
      missingDependencyPreservation brokenReconstruction replayRejected
      recompute diagnostic ->
    ay_pirc_NoSemanticClaim diagnostic := by
  intro log_entry
  exact ay_pirc_conj_right
    (ay_pirc_RecomputeObligation currentCnf recompute)
    (ay_pirc_NoSemanticClaim diagnostic)
    (ay_pirc_conj_right
      (ay_pirc_EpochFailure
        staleFingerprint missingDependencyPreservation
        brokenReconstruction replayRejected)
      (ay_pirc_Conj
        (ay_pirc_RecomputeObligation currentCnf recompute)
        (ay_pirc_NoSemanticClaim diagnostic))
      (ay_pirc_conj_left
        (ay_pirc_Conj
          (ay_pirc_EpochFailure
            staleFingerprint missingDependencyPreservation
            brokenReconstruction replayRejected)
          (ay_pirc_Conj
            (ay_pirc_RecomputeObligation currentCnf recompute)
            (ay_pirc_NoSemanticClaim diagnostic)))
        nextLog
        (ay_pirc_conj_right previousLog
          (ay_pirc_Conj
            (ay_pirc_Conj
              (ay_pirc_EpochFailure
                staleFingerprint missingDependencyPreservation
                brokenReconstruction replayRejected)
              (ay_pirc_Conj
                (ay_pirc_RecomputeObligation currentCnf recompute)
                (ay_pirc_NoSemanticClaim diagnostic)))
            nextLog)
          log_entry)))

theorem ay_pirc_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleFingerprint : Prop) (missingDependencyPreservation : Prop)
    (brokenReconstruction : Prop) (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pirc_DiagnosticEpochLogEntry
      previousLog nextLog currentCnf staleFingerprint
      missingDependencyPreservation brokenReconstruction replayRejected
      recompute diagnostic ->
    ay_pirc_RecomputeObligation currentCnf recompute := by
  intro log_entry
  exact ay_pirc_conj_left
    (ay_pirc_RecomputeObligation currentCnf recompute)
    (ay_pirc_NoSemanticClaim diagnostic)
    (ay_pirc_conj_right
      (ay_pirc_EpochFailure
        staleFingerprint missingDependencyPreservation
        brokenReconstruction replayRejected)
      (ay_pirc_Conj
        (ay_pirc_RecomputeObligation currentCnf recompute)
        (ay_pirc_NoSemanticClaim diagnostic))
      (ay_pirc_conj_left
        (ay_pirc_Conj
          (ay_pirc_EpochFailure
            staleFingerprint missingDependencyPreservation
            brokenReconstruction replayRejected)
          (ay_pirc_Conj
            (ay_pirc_RecomputeObligation currentCnf recompute)
            (ay_pirc_NoSemanticClaim diagnostic)))
        nextLog
        (ay_pirc_conj_right previousLog
          (ay_pirc_Conj
            (ay_pirc_Conj
              (ay_pirc_EpochFailure
                staleFingerprint missingDependencyPreservation
                brokenReconstruction replayRejected)
              (ay_pirc_Conj
                (ay_pirc_RecomputeObligation currentCnf recompute)
                (ay_pirc_NoSemanticClaim diagnostic)))
            nextLog)
          log_entry)))

theorem ay_pirc_failure_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleFingerprint : Prop) (missingDependencyPreservation : Prop)
    (brokenReconstruction : Prop) (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pirc_DiagnosticEpochLogEntry
      previousLog nextLog currentCnf staleFingerprint
      missingDependencyPreservation brokenReconstruction replayRejected
      recompute diagnostic ->
    ay_pirc_Conj
      (ay_pirc_EpochFailure
        staleFingerprint missingDependencyPreservation
        brokenReconstruction replayRejected)
      (ay_pirc_Conj
        (ay_pirc_RecomputeObligation currentCnf recompute)
        (ay_pirc_NoSemanticClaim diagnostic)) := by
  intro log_entry
  exact ay_pirc_conj_intro
    (ay_pirc_EpochFailure
      staleFingerprint missingDependencyPreservation
      brokenReconstruction replayRejected)
    (ay_pirc_Conj
      (ay_pirc_RecomputeObligation currentCnf recompute)
      (ay_pirc_NoSemanticClaim diagnostic))
    (ay_pirc_diagnostic_failure previousLog nextLog currentCnf
      staleFingerprint missingDependencyPreservation brokenReconstruction
      replayRejected recompute diagnostic log_entry)
    (ay_pirc_conj_intro
      (ay_pirc_RecomputeObligation currentCnf recompute)
      (ay_pirc_NoSemanticClaim diagnostic)
      (ay_pirc_diagnostic_recompute previousLog nextLog currentCnf
        staleFingerprint missingDependencyPreservation brokenReconstruction
        replayRejected recompute diagnostic log_entry)
      (ay_pirc_diagnostic_no_claim previousLog nextLog currentCnf
        staleFingerprint missingDependencyPreservation brokenReconstruction
        replayRejected recompute diagnostic log_entry))
