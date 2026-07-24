-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Self-subsuming-resolution replay soundness for preprocessing. The
-- propositions stand for pivot literal lineage, parent coverage, strengthened
-- clause ID lineage, deletion/retention records, model/proof reconstruction
-- hooks, digest membership, checker replay, original-instance fingerprint
-- agreement, diagnostics, and public SAT/UNSAT reports.

def ay_pssr_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pssr_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pssr_Equisat (before : Prop) (after : Prop) :=
  ay_pssr_Conj (before -> after) (after -> before)

def ay_pssr_Sat (cnf : Prop) (model : Prop) :=
  ay_pssr_Conj cnf model

def ay_pssr_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pssr_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pssr_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pssr_PivotLineage
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop) :=
  ay_pssr_Conj pivotWitness
    (ay_pssr_IdMatch originalPivot replayedPivot)

def ay_pssr_ParentCoverage
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop) :=
  ay_pssr_Conj coverageWitness
    (ay_pssr_Conj leftParent
      (ay_pssr_Conj rightParent coveredParents))

def ay_pssr_StrengthenedClauseLineage
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop) :=
  ay_pssr_Conj lineageWitness
    (ay_pssr_IdMatch originalClauseId strengthenedClauseId)

def ay_pssr_DeletionRetentionRecord
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop) :=
  ay_pssr_Conj retentionWitness
    (ay_pssr_Conj deletedLiteral retainedClause)

def ay_pssr_ModelReconstruction
    (afterCnf : Prop) (beforeCnf : Prop)
    (afterModel : Prop) (beforeModel : Prop) :=
  ay_pssr_Sat afterCnf afterModel ->
    ay_pssr_Sat beforeCnf beforeModel

def ay_pssr_ProofReconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pssr_Replay afterCnf certificate conflict ->
    certificate -> beforeCnf -> conflict

def ay_pssr_DigestMembership
    (ssrDigest : Prop) (manifestDigest : Prop) :=
  ay_pssr_Conj ssrDigest manifestDigest

def ay_pssr_CheckerReplay
    (ssrCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pssr_Conj ssrCertificate checkerAccepted

def ay_pssr_FingerprintAgreement
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pssr_Conj fingerprintWitness
    (ay_pssr_IdMatch originalFingerprint replayFingerprint)

def ay_pssr_AcceptedSsrReplay
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pssr_Conj
    (ay_pssr_PivotLineage originalPivot replayedPivot pivotWitness)
    (ay_pssr_Conj
      (ay_pssr_ParentCoverage
        leftParent rightParent coveredParents coverageWitness)
      (ay_pssr_Conj
        (ay_pssr_StrengthenedClauseLineage
          originalClauseId strengthenedClauseId lineageWitness)
        (ay_pssr_Conj
          (ay_pssr_DeletionRetentionRecord
            deletedLiteral retainedClause retentionWitness)
          (ay_pssr_Conj
            (ay_pssr_Equisat beforeCnf afterCnf)
            (ay_pssr_Conj
              (ay_pssr_ModelReconstruction
                afterCnf beforeCnf afterModel beforeModel)
              (ay_pssr_Conj
                (ay_pssr_ProofReconstruction
                  beforeCnf afterCnf certificate conflict)
                (ay_pssr_Conj
                  (ay_pssr_DigestMembership ssrDigest manifestDigest)
                  (ay_pssr_Conj
                    (ay_pssr_CheckerReplay
                      ssrCertificate checkerAccepted)
                    (ay_pssr_FingerprintAgreement
                      originalFingerprint replayFingerprint
                      fingerprintWitness)))))))))

def ay_pssr_AcceptedSsrLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pssr_Conj previousLog
    (ay_pssr_Conj
      (ay_pssr_AcceptedSsrReplay
        beforeCnf afterCnf originalPivot replayedPivot pivotWitness
        leftParent rightParent coveredParents coverageWitness originalClauseId
        strengthenedClauseId lineageWitness deletedLiteral retainedClause
        retentionWitness afterModel beforeModel certificate conflict ssrDigest
        manifestDigest ssrCertificate checkerAccepted originalFingerprint
        replayFingerprint fingerprintWitness)
      nextLog)

def ay_pssr_ReplayFailure
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :=
  ay_pssr_Disj missingPivotLineage
    (ay_pssr_Disj staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))))

def ay_pssr_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pssr_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pssr_Conj currentCnf recompute

def ay_pssr_DiagnosticSsrLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pssr_Conj previousLog
    (ay_pssr_Conj
      (ay_pssr_Conj
        (ay_pssr_ReplayFailure
          missingPivotLineage staleParents badStrengthenedClause
          unretainedDeletion brokenReconstruction digestMismatch
          replayRejected fingerprintDrift)
        (ay_pssr_Conj
          (ay_pssr_RecomputeObligation currentCnf recompute)
          (ay_pssr_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pssr_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pssr_Conj exitCode claim

def ay_pssr_PublicResult
    (beforeCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pssr_Disj
    (ay_pssr_ExitCodeSound exitCode (ay_pssr_Sat beforeCnf model))
    (ay_pssr_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))

theorem ay_pssr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pssr_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pssr_conj_left
    (left : Prop) (right : Prop) :
    ay_pssr_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pssr_conj_right
    (left : Prop) (right : Prop) :
    ay_pssr_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pssr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pssr_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pssr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pssr_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pssr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pssr_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pssr_conj_left (before -> after) (after -> before) eq

theorem ay_pssr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pssr_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pssr_conj_right (before -> after) (after -> before) eq

theorem ay_pssr_replay_pivot_lineage
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_PivotLineage originalPivot replayedPivot pivotWitness := by
  intro accepted
  exact ay_pssr_conj_left
    (ay_pssr_PivotLineage originalPivot replayedPivot pivotWitness)
    (ay_pssr_Conj
      (ay_pssr_ParentCoverage
        leftParent rightParent coveredParents coverageWitness)
      (ay_pssr_Conj
        (ay_pssr_StrengthenedClauseLineage
          originalClauseId strengthenedClauseId lineageWitness)
        (ay_pssr_Conj
          (ay_pssr_DeletionRetentionRecord
            deletedLiteral retainedClause retentionWitness)
          (ay_pssr_Conj
            (ay_pssr_Equisat beforeCnf afterCnf)
            (ay_pssr_Conj
              (ay_pssr_ModelReconstruction
                afterCnf beforeCnf afterModel beforeModel)
              (ay_pssr_Conj
                (ay_pssr_ProofReconstruction
                  beforeCnf afterCnf certificate conflict)
                (ay_pssr_Conj
                  (ay_pssr_DigestMembership ssrDigest manifestDigest)
                  (ay_pssr_Conj
                    (ay_pssr_CheckerReplay
                      ssrCertificate checkerAccepted)
                    (ay_pssr_FingerprintAgreement
                      originalFingerprint replayFingerprint
                      fingerprintWitness)))))))))
    accepted

theorem ay_pssr_replay_parent_coverage
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_ParentCoverage leftParent rightParent coveredParents
      coverageWitness := by
  intro accepted
  exact accepted
    (ay_pssr_ParentCoverage leftParent rightParent coveredParents
      coverageWitness)
    (fun _pivot rest1 =>
      rest1
        (ay_pssr_ParentCoverage leftParent rightParent coveredParents
          coverageWitness)
        (fun parents _tail => parents))

theorem ay_pssr_replay_strengthened_lineage
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_StrengthenedClauseLineage
      originalClauseId strengthenedClauseId lineageWitness := by
  intro accepted
  exact accepted
    (ay_pssr_StrengthenedClauseLineage
      originalClauseId strengthenedClauseId lineageWitness)
    (fun _pivot rest1 =>
      rest1
        (ay_pssr_StrengthenedClauseLineage
          originalClauseId strengthenedClauseId lineageWitness)
        (fun _parents rest2 =>
          rest2
            (ay_pssr_StrengthenedClauseLineage
              originalClauseId strengthenedClauseId lineageWitness)
            (fun lineage _tail => lineage)))

theorem ay_pssr_replay_deletion_retention
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_DeletionRetentionRecord
      deletedLiteral retainedClause retentionWitness := by
  intro accepted
  exact accepted
    (ay_pssr_DeletionRetentionRecord
      deletedLiteral retainedClause retentionWitness)
    (fun _pivot rest1 =>
      rest1
        (ay_pssr_DeletionRetentionRecord
          deletedLiteral retainedClause retentionWitness)
        (fun _parents rest2 =>
          rest2
            (ay_pssr_DeletionRetentionRecord
              deletedLiteral retainedClause retentionWitness)
            (fun _lineage rest3 =>
              rest3
                (ay_pssr_DeletionRetentionRecord
                  deletedLiteral retainedClause retentionWitness)
                (fun record _tail => record))))

theorem ay_pssr_replay_equisat
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_Equisat beforeCnf afterCnf := by
  intro accepted
  exact accepted
    (ay_pssr_Equisat beforeCnf afterCnf)
    (fun _pivot rest1 =>
      rest1
        (ay_pssr_Equisat beforeCnf afterCnf)
        (fun _parents rest2 =>
          rest2
            (ay_pssr_Equisat beforeCnf afterCnf)
            (fun _lineage rest3 =>
              rest3
                (ay_pssr_Equisat beforeCnf afterCnf)
                (fun _record rest4 =>
                  rest4
                    (ay_pssr_Equisat beforeCnf afterCnf)
                    (fun eq _tail => eq)))))

theorem ay_pssr_replay_model_reconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_ModelReconstruction afterCnf beforeCnf afterModel beforeModel := by
  intro accepted
  exact accepted
    (ay_pssr_ModelReconstruction afterCnf beforeCnf afterModel beforeModel)
    (fun _pivot rest1 =>
      rest1
        (ay_pssr_ModelReconstruction afterCnf beforeCnf afterModel beforeModel)
        (fun _parents rest2 =>
          rest2
            (ay_pssr_ModelReconstruction
              afterCnf beforeCnf afterModel beforeModel)
            (fun _lineage rest3 =>
              rest3
                (ay_pssr_ModelReconstruction
                  afterCnf beforeCnf afterModel beforeModel)
                (fun _record rest4 =>
                  rest4
                    (ay_pssr_ModelReconstruction
                      afterCnf beforeCnf afterModel beforeModel)
                    (fun _eq rest5 =>
                      rest5
                        (ay_pssr_ModelReconstruction
                          afterCnf beforeCnf afterModel beforeModel)
                        (fun model _tail => model))))))

theorem ay_pssr_replay_proof_reconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_ProofReconstruction beforeCnf afterCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_pssr_ProofReconstruction beforeCnf afterCnf certificate conflict)
    (fun _pivot rest1 =>
      rest1
        (ay_pssr_ProofReconstruction beforeCnf afterCnf certificate conflict)
        (fun _parents rest2 =>
          rest2
            (ay_pssr_ProofReconstruction
              beforeCnf afterCnf certificate conflict)
            (fun _lineage rest3 =>
              rest3
                (ay_pssr_ProofReconstruction
                  beforeCnf afterCnf certificate conflict)
                (fun _record rest4 =>
                  rest4
                    (ay_pssr_ProofReconstruction
                      beforeCnf afterCnf certificate conflict)
                    (fun _eq rest5 =>
                      rest5
                        (ay_pssr_ProofReconstruction
                          beforeCnf afterCnf certificate conflict)
                        (fun _model rest6 =>
                          rest6
                            (ay_pssr_ProofReconstruction
                              beforeCnf afterCnf certificate conflict)
                            (fun proof _tail => proof)))))))

theorem ay_pssr_replay_digest
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_DigestMembership ssrDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_pssr_DigestMembership ssrDigest manifestDigest)
    (fun _pivot rest1 =>
      rest1
        (ay_pssr_DigestMembership ssrDigest manifestDigest)
        (fun _parents rest2 =>
          rest2
            (ay_pssr_DigestMembership ssrDigest manifestDigest)
            (fun _lineage rest3 =>
              rest3
                (ay_pssr_DigestMembership ssrDigest manifestDigest)
                (fun _record rest4 =>
                  rest4
                    (ay_pssr_DigestMembership ssrDigest manifestDigest)
                    (fun _eq rest5 =>
                      rest5
                        (ay_pssr_DigestMembership ssrDigest manifestDigest)
                        (fun _model rest6 =>
                          rest6
                            (ay_pssr_DigestMembership ssrDigest manifestDigest)
                            (fun _proof rest7 =>
                              rest7
                                (ay_pssr_DigestMembership
                                  ssrDigest manifestDigest)
                                (fun digest _tail => digest))))))))

theorem ay_pssr_replay_checker
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_CheckerReplay ssrCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pssr_CheckerReplay ssrCertificate checkerAccepted)
    (fun _pivot rest1 =>
      rest1
        (ay_pssr_CheckerReplay ssrCertificate checkerAccepted)
        (fun _parents rest2 =>
          rest2
            (ay_pssr_CheckerReplay ssrCertificate checkerAccepted)
            (fun _lineage rest3 =>
              rest3
                (ay_pssr_CheckerReplay ssrCertificate checkerAccepted)
                (fun _record rest4 =>
                  rest4
                    (ay_pssr_CheckerReplay ssrCertificate checkerAccepted)
                    (fun _eq rest5 =>
                      rest5
                        (ay_pssr_CheckerReplay ssrCertificate checkerAccepted)
                        (fun _model rest6 =>
                          rest6
                            (ay_pssr_CheckerReplay
                              ssrCertificate checkerAccepted)
                            (fun _proof rest7 =>
                              rest7
                                (ay_pssr_CheckerReplay
                                  ssrCertificate checkerAccepted)
                                (fun _digest rest8 =>
                                  rest8
                                    (ay_pssr_CheckerReplay
                                      ssrCertificate checkerAccepted)
                                    (fun checker _tail => checker)))))))))

theorem ay_pssr_replay_fingerprint
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_FingerprintAgreement
      originalFingerprint replayFingerprint fingerprintWitness := by
  intro accepted
  exact accepted
    (ay_pssr_FingerprintAgreement
      originalFingerprint replayFingerprint fingerprintWitness)
    (fun _pivot rest1 =>
      rest1
        (ay_pssr_FingerprintAgreement
          originalFingerprint replayFingerprint fingerprintWitness)
        (fun _parents rest2 =>
          rest2
            (ay_pssr_FingerprintAgreement
              originalFingerprint replayFingerprint fingerprintWitness)
            (fun _lineage rest3 =>
              rest3
                (ay_pssr_FingerprintAgreement
                  originalFingerprint replayFingerprint fingerprintWitness)
                (fun _record rest4 =>
                  rest4
                    (ay_pssr_FingerprintAgreement
                      originalFingerprint replayFingerprint fingerprintWitness)
                    (fun _eq rest5 =>
                      rest5
                        (ay_pssr_FingerprintAgreement
                          originalFingerprint replayFingerprint
                          fingerprintWitness)
                        (fun _model rest6 =>
                          rest6
                            (ay_pssr_FingerprintAgreement
                              originalFingerprint replayFingerprint
                              fingerprintWitness)
                            (fun _proof rest7 =>
                              rest7
                                (ay_pssr_FingerprintAgreement
                                  originalFingerprint replayFingerprint
                                  fingerprintWitness)
                                (fun _digest rest8 =>
                                  rest8
                                    (ay_pssr_FingerprintAgreement
                                      originalFingerprint replayFingerprint
                                      fingerprintWitness)
                                    (fun _checker fp => fp)))))))))

theorem ay_pssr_sat_pullback
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_Sat afterCnf afterModel ->
    ay_pssr_Sat beforeCnf beforeModel := by
  intro accepted afterSat
  exact
    (ay_pssr_replay_model_reconstruction
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness leftParent
      rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness accepted)
      afterSat

theorem ay_pssr_unsat_pushback
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_Replay afterCnf certificate conflict ->
    certificate ->
    beforeCnf ->
    conflict := by
  intro accepted replay cert before
  exact
    (ay_pssr_replay_proof_reconstruction
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness leftParent
      rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness accepted)
      replay cert before

theorem ay_pssr_public_sat
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_Sat afterCnf afterModel ->
    exitCode ->
    ay_pssr_PublicResult beforeCnf beforeModel certificate conflict exitCode := by
  intro accepted afterSat exit
  exact ay_pssr_disj_left
    (ay_pssr_ExitCodeSound exitCode (ay_pssr_Sat beforeCnf beforeModel))
    (ay_pssr_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))
    (ay_pssr_conj_intro exitCode
      (ay_pssr_Sat beforeCnf beforeModel)
      exit
      (ay_pssr_sat_pullback
        beforeCnf afterCnf originalPivot replayedPivot pivotWitness leftParent
        rightParent coveredParents coverageWitness originalClauseId
        strengthenedClauseId lineageWitness deletedLiteral retainedClause
        retentionWitness afterModel beforeModel certificate conflict ssrDigest
        manifestDigest ssrCertificate checkerAccepted originalFingerprint
        replayFingerprint fingerprintWitness accepted afterSat))

theorem ay_pssr_public_unsat
    (beforeCnf : Prop) (afterCnf : Prop)
    (originalPivot : Prop) (replayedPivot : Prop)
    (pivotWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (originalClauseId : Prop) (strengthenedClauseId : Prop)
    (lineageWitness : Prop)
    (deletedLiteral : Prop) (retainedClause : Prop)
    (retentionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (ssrDigest : Prop) (manifestDigest : Prop)
    (ssrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pssr_AcceptedSsrReplay
      beforeCnf afterCnf originalPivot replayedPivot pivotWitness
      leftParent rightParent coveredParents coverageWitness originalClauseId
      strengthenedClauseId lineageWitness deletedLiteral retainedClause
      retentionWitness afterModel beforeModel certificate conflict ssrDigest
      manifestDigest ssrCertificate checkerAccepted originalFingerprint
      replayFingerprint fingerprintWitness ->
    ay_pssr_Replay afterCnf certificate conflict ->
    exitCode ->
    ay_pssr_PublicResult beforeCnf beforeModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_pssr_disj_right
    (ay_pssr_ExitCodeSound exitCode (ay_pssr_Sat beforeCnf beforeModel))
    (ay_pssr_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))
    (ay_pssr_conj_intro exitCode
      (certificate -> beforeCnf -> conflict)
      exit
      (fun cert before =>
        ay_pssr_unsat_pushback
          beforeCnf afterCnf originalPivot replayedPivot pivotWitness
          leftParent rightParent coveredParents coverageWitness originalClauseId
          strengthenedClauseId lineageWitness deletedLiteral retainedClause
          retentionWitness afterModel beforeModel certificate conflict ssrDigest
          manifestDigest ssrCertificate checkerAccepted originalFingerprint
          replayFingerprint fingerprintWitness accepted replay cert before))

theorem ay_pssr_failure_missing_pivot_lineage
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    missingPivotLineage ->
    ay_pssr_ReplayFailure
      missingPivotLineage staleParents badStrengthenedClause unretainedDeletion
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro missing
  exact ay_pssr_disj_left missingPivotLineage
    (ay_pssr_Disj staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))))
    missing

theorem ay_pssr_failure_stale_parents
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    staleParents ->
    ay_pssr_ReplayFailure
      missingPivotLineage staleParents badStrengthenedClause unretainedDeletion
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro stale
  exact ay_pssr_disj_right missingPivotLineage
    (ay_pssr_Disj staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))))
    (ay_pssr_disj_left staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)))))
      stale)

theorem ay_pssr_failure_bad_strengthened_clause
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    badStrengthenedClause ->
    ay_pssr_ReplayFailure
      missingPivotLineage staleParents badStrengthenedClause unretainedDeletion
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro bad
  exact ay_pssr_disj_right missingPivotLineage
    (ay_pssr_Disj staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))))
    (ay_pssr_disj_right staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)))))
      (ay_pssr_disj_left badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))
        bad))

theorem ay_pssr_failure_unretained_deletion
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    unretainedDeletion ->
    ay_pssr_ReplayFailure
      missingPivotLineage staleParents badStrengthenedClause unretainedDeletion
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro unretained
  exact ay_pssr_disj_right missingPivotLineage
    (ay_pssr_Disj staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))))
    (ay_pssr_disj_right staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)))))
      (ay_pssr_disj_right badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))
        (ay_pssr_disj_left unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)))
          unretained)))

theorem ay_pssr_failure_broken_reconstruction
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    brokenReconstruction ->
    ay_pssr_ReplayFailure
      missingPivotLineage staleParents badStrengthenedClause unretainedDeletion
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro broken
  exact ay_pssr_disj_right missingPivotLineage
    (ay_pssr_Disj staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))))
    (ay_pssr_disj_right staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)))))
      (ay_pssr_disj_right badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))
        (ay_pssr_disj_right unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)))
          (ay_pssr_disj_left brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))
            broken))))

theorem ay_pssr_failure_digest_mismatch
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    digestMismatch ->
    ay_pssr_ReplayFailure
      missingPivotLineage staleParents badStrengthenedClause unretainedDeletion
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro mismatch
  exact ay_pssr_disj_right missingPivotLineage
    (ay_pssr_Disj staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))))
    (ay_pssr_disj_right staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)))))
      (ay_pssr_disj_right badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))
        (ay_pssr_disj_right unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)))
          (ay_pssr_disj_right brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))
            (ay_pssr_disj_left digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)
              mismatch)))))

theorem ay_pssr_failure_replay_rejected
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    replayRejected ->
    ay_pssr_ReplayFailure
      missingPivotLineage staleParents badStrengthenedClause unretainedDeletion
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro rejected
  exact ay_pssr_disj_right missingPivotLineage
    (ay_pssr_Disj staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))))
    (ay_pssr_disj_right staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)))))
      (ay_pssr_disj_right badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))
        (ay_pssr_disj_right unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)))
          (ay_pssr_disj_right brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))
            (ay_pssr_disj_right digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)
              (ay_pssr_disj_left replayRejected fingerprintDrift rejected))))))

theorem ay_pssr_failure_fingerprint_drift
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop) :
    fingerprintDrift ->
    ay_pssr_ReplayFailure
      missingPivotLineage staleParents badStrengthenedClause unretainedDeletion
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro drift
  exact ay_pssr_disj_right missingPivotLineage
    (ay_pssr_Disj staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))))
    (ay_pssr_disj_right staleParents
      (ay_pssr_Disj badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)))))
      (ay_pssr_disj_right badStrengthenedClause
        (ay_pssr_Disj unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))))
        (ay_pssr_disj_right unretainedDeletion
          (ay_pssr_Disj brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)))
          (ay_pssr_disj_right brokenReconstruction
            (ay_pssr_Disj digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift))
            (ay_pssr_disj_right digestMismatch
              (ay_pssr_Disj replayRejected fingerprintDrift)
              (ay_pssr_disj_right replayRejected fingerprintDrift drift))))))

theorem ay_pssr_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pssr_DiagnosticSsrLogEntry
      previousLog nextLog currentCnf missingPivotLineage staleParents
      badStrengthenedClause unretainedDeletion brokenReconstruction
      digestMismatch replayRejected fingerprintDrift recompute diagnostic ->
    ay_pssr_ReplayFailure
      missingPivotLineage staleParents badStrengthenedClause unretainedDeletion
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro entry
  exact entry
    (ay_pssr_ReplayFailure
      missingPivotLineage staleParents badStrengthenedClause unretainedDeletion
      brokenReconstruction digestMismatch replayRejected fingerprintDrift)
    (fun _previous rest1 =>
      rest1
        (ay_pssr_ReplayFailure
          missingPivotLineage staleParents badStrengthenedClause
          unretainedDeletion brokenReconstruction digestMismatch replayRejected
          fingerprintDrift)
        (fun body _next =>
          body
            (ay_pssr_ReplayFailure
              missingPivotLineage staleParents badStrengthenedClause
              unretainedDeletion brokenReconstruction digestMismatch
              replayRejected fingerprintDrift)
            (fun failure _tail => failure)))

theorem ay_pssr_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pssr_DiagnosticSsrLogEntry
      previousLog nextLog currentCnf missingPivotLineage staleParents
      badStrengthenedClause unretainedDeletion brokenReconstruction
      digestMismatch replayRejected fingerprintDrift recompute diagnostic ->
    ay_pssr_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_pssr_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_pssr_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_pssr_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_pssr_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_pssr_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pssr_DiagnosticSsrLogEntry
      previousLog nextLog currentCnf missingPivotLineage staleParents
      badStrengthenedClause unretainedDeletion brokenReconstruction
      digestMismatch replayRejected fingerprintDrift recompute diagnostic ->
    ay_pssr_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_pssr_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_pssr_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_pssr_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_pssr_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_pssr_failure_no_claim
    (missingPivotLineage : Prop) (staleParents : Prop)
    (badStrengthenedClause : Prop) (unretainedDeletion : Prop)
    (brokenReconstruction : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (fingerprintDrift : Prop)
    (diagnostic : Prop) :
    ay_pssr_ReplayFailure
      missingPivotLineage staleParents badStrengthenedClause unretainedDeletion
      brokenReconstruction digestMismatch replayRejected fingerprintDrift ->
    diagnostic ->
    ay_pssr_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
