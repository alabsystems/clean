-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Resolution proof-link soundness for preprocessing. The propositions stand
-- for stable clause identifiers, parent coverage, digest membership, checker
-- replay, model/proof reconstruction hooks, original-instance fingerprint
-- lineage, diagnostics, and public SAT/UNSAT reports.

def ay_prpl_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_prpl_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_prpl_Equisat (before : Prop) (after : Prop) :=
  ay_prpl_Conj (before -> after) (after -> before)

def ay_prpl_Sat (cnf : Prop) (model : Prop) :=
  ay_prpl_Conj cnf model

def ay_prpl_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_prpl_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_prpl_Conj (leftId -> rightId) (rightId -> leftId)

def ay_prpl_StableClauseIds
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop) :=
  ay_prpl_Conj stabilityWitness
    (ay_prpl_IdMatch emittedClauseId replayedClauseId)

def ay_prpl_ParentCoverage
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop) :=
  ay_prpl_Conj coverageWitness
    (ay_prpl_Conj leftParent
      (ay_prpl_Conj rightParent coveredParents))

def ay_prpl_DigestMembership
    (proofLinkDigest : Prop) (manifestDigest : Prop) :=
  ay_prpl_Conj proofLinkDigest manifestDigest

def ay_prpl_CheckerReplay
    (proofLinkCertificate : Prop) (checkerAccepted : Prop) :=
  ay_prpl_Conj proofLinkCertificate checkerAccepted

def ay_prpl_ModelReconstruction
    (afterCnf : Prop) (beforeCnf : Prop)
    (afterModel : Prop) (beforeModel : Prop) :=
  ay_prpl_Sat afterCnf afterModel ->
    ay_prpl_Sat beforeCnf beforeModel

def ay_prpl_ProofReconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_prpl_Replay afterCnf certificate conflict ->
    certificate -> beforeCnf -> conflict

def ay_prpl_FingerprintLineage
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop) :=
  ay_prpl_Conj lineageWitness
    (ay_prpl_IdMatch originalFingerprint preprocessedFingerprint)

def ay_prpl_AcceptedProofLink
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop) :=
  ay_prpl_Conj
    (ay_prpl_StableClauseIds
      emittedClauseId replayedClauseId stabilityWitness)
    (ay_prpl_Conj
      (ay_prpl_ParentCoverage
        leftParent rightParent coveredParents coverageWitness)
      (ay_prpl_Conj
        (ay_prpl_DigestMembership proofLinkDigest manifestDigest)
        (ay_prpl_Conj
          (ay_prpl_CheckerReplay proofLinkCertificate checkerAccepted)
          (ay_prpl_Conj
            (ay_prpl_Equisat beforeCnf afterCnf)
            (ay_prpl_Conj
              (ay_prpl_ModelReconstruction
                afterCnf beforeCnf afterModel beforeModel)
              (ay_prpl_Conj
                (ay_prpl_ProofReconstruction
                  beforeCnf afterCnf certificate conflict)
                (ay_prpl_FingerprintLineage
                  originalFingerprint preprocessedFingerprint
                  lineageWitness)))))))

def ay_prpl_AcceptedProofLinkLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop) :=
  ay_prpl_Conj previousLog
    (ay_prpl_Conj
      (ay_prpl_AcceptedProofLink
        beforeCnf afterCnf emittedClauseId replayedClauseId
        stabilityWitness leftParent rightParent coveredParents
        coverageWitness proofLinkDigest manifestDigest proofLinkCertificate
        checkerAccepted afterModel beforeModel certificate conflict
        originalFingerprint preprocessedFingerprint lineageWitness)
      nextLog)

def ay_prpl_LinkFailure
    (staleClauseId : Prop) (missingParentCoverage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (brokenReconstruction : Prop) (staleFingerprint : Prop) :=
  ay_prpl_Disj staleClauseId
    (ay_prpl_Disj missingParentCoverage
      (ay_prpl_Disj digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint))))

def ay_prpl_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_prpl_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_prpl_Conj currentCnf recompute

def ay_prpl_DiagnosticProofLinkLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleClauseId : Prop) (missingParentCoverage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (brokenReconstruction : Prop) (staleFingerprint : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_prpl_Conj previousLog
    (ay_prpl_Conj
      (ay_prpl_Conj
        (ay_prpl_LinkFailure
          staleClauseId missingParentCoverage digestMismatch replayRejected
          brokenReconstruction staleFingerprint)
        (ay_prpl_Conj
          (ay_prpl_RecomputeObligation currentCnf recompute)
          (ay_prpl_NoSemanticClaim diagnostic)))
      nextLog)

def ay_prpl_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_prpl_Conj exitCode claim

def ay_prpl_PublicResult
    (beforeCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_prpl_Disj
    (ay_prpl_ExitCodeSound exitCode (ay_prpl_Sat beforeCnf model))
    (ay_prpl_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))

theorem ay_prpl_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_prpl_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_prpl_conj_left
    (left : Prop) (right : Prop) :
    ay_prpl_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_prpl_conj_right
    (left : Prop) (right : Prop) :
    ay_prpl_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_prpl_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_prpl_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_prpl_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_prpl_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_prpl_equisat_forward
    (before : Prop) (after : Prop) :
    ay_prpl_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_prpl_conj_left (before -> after) (after -> before) eq

theorem ay_prpl_equisat_backward
    (before : Prop) (after : Prop) :
    ay_prpl_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_prpl_conj_right (before -> after) (after -> before) eq

theorem ay_prpl_link_clause_ids
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop) :
    ay_prpl_AcceptedProofLink
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness ->
    ay_prpl_StableClauseIds
      emittedClauseId replayedClauseId stabilityWitness := by
  intro accepted
  exact ay_prpl_conj_left
    (ay_prpl_StableClauseIds
      emittedClauseId replayedClauseId stabilityWitness)
    (ay_prpl_Conj
      (ay_prpl_ParentCoverage
        leftParent rightParent coveredParents coverageWitness)
      (ay_prpl_Conj
        (ay_prpl_DigestMembership proofLinkDigest manifestDigest)
        (ay_prpl_Conj
          (ay_prpl_CheckerReplay proofLinkCertificate checkerAccepted)
          (ay_prpl_Conj
            (ay_prpl_Equisat beforeCnf afterCnf)
            (ay_prpl_Conj
              (ay_prpl_ModelReconstruction
                afterCnf beforeCnf afterModel beforeModel)
              (ay_prpl_Conj
                (ay_prpl_ProofReconstruction
                  beforeCnf afterCnf certificate conflict)
                (ay_prpl_FingerprintLineage
                  originalFingerprint preprocessedFingerprint
                  lineageWitness)))))))
    accepted

theorem ay_prpl_link_parent_coverage
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop) :
    ay_prpl_AcceptedProofLink
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness ->
    ay_prpl_ParentCoverage
      leftParent rightParent coveredParents coverageWitness := by
  intro accepted
  exact accepted
    (ay_prpl_ParentCoverage
      leftParent rightParent coveredParents coverageWitness)
    (fun _ids rest1 =>
      rest1
        (ay_prpl_ParentCoverage
          leftParent rightParent coveredParents coverageWitness)
        (fun parents _tail => parents))

theorem ay_prpl_link_digest
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop) :
    ay_prpl_AcceptedProofLink
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness ->
    ay_prpl_DigestMembership proofLinkDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_prpl_DigestMembership proofLinkDigest manifestDigest)
    (fun _ids rest1 =>
      rest1
        (ay_prpl_DigestMembership proofLinkDigest manifestDigest)
        (fun _parents rest2 =>
          rest2
            (ay_prpl_DigestMembership proofLinkDigest manifestDigest)
            (fun digest _tail => digest)))

theorem ay_prpl_link_checker
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop) :
    ay_prpl_AcceptedProofLink
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness ->
    ay_prpl_CheckerReplay proofLinkCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_prpl_CheckerReplay proofLinkCertificate checkerAccepted)
    (fun _ids rest1 =>
      rest1
        (ay_prpl_CheckerReplay proofLinkCertificate checkerAccepted)
        (fun _parents rest2 =>
          rest2
            (ay_prpl_CheckerReplay proofLinkCertificate checkerAccepted)
            (fun _digest rest3 =>
              rest3
                (ay_prpl_CheckerReplay proofLinkCertificate checkerAccepted)
                (fun checker _tail => checker))))

theorem ay_prpl_link_equisat
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop) :
    ay_prpl_AcceptedProofLink
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness ->
    ay_prpl_Equisat beforeCnf afterCnf := by
  intro accepted
  exact accepted
    (ay_prpl_Equisat beforeCnf afterCnf)
    (fun _ids rest1 =>
      rest1
        (ay_prpl_Equisat beforeCnf afterCnf)
        (fun _parents rest2 =>
          rest2
            (ay_prpl_Equisat beforeCnf afterCnf)
            (fun _digest rest3 =>
              rest3
                (ay_prpl_Equisat beforeCnf afterCnf)
                (fun _checker rest4 =>
                  rest4
                    (ay_prpl_Equisat beforeCnf afterCnf)
                    (fun eq _tail => eq)))))

theorem ay_prpl_link_model_reconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop) :
    ay_prpl_AcceptedProofLink
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness ->
    ay_prpl_ModelReconstruction afterCnf beforeCnf afterModel beforeModel := by
  intro accepted
  exact accepted
    (ay_prpl_ModelReconstruction afterCnf beforeCnf afterModel beforeModel)
    (fun _ids rest1 =>
      rest1
        (ay_prpl_ModelReconstruction afterCnf beforeCnf afterModel beforeModel)
        (fun _parents rest2 =>
          rest2
            (ay_prpl_ModelReconstruction
              afterCnf beforeCnf afterModel beforeModel)
            (fun _digest rest3 =>
              rest3
                (ay_prpl_ModelReconstruction
                  afterCnf beforeCnf afterModel beforeModel)
                (fun _checker rest4 =>
                  rest4
                    (ay_prpl_ModelReconstruction
                      afterCnf beforeCnf afterModel beforeModel)
                    (fun _eq rest5 =>
                      rest5
                        (ay_prpl_ModelReconstruction
                          afterCnf beforeCnf afterModel beforeModel)
                        (fun model _tail => model))))))

theorem ay_prpl_link_proof_reconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop) :
    ay_prpl_AcceptedProofLink
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness ->
    ay_prpl_ProofReconstruction beforeCnf afterCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_prpl_ProofReconstruction beforeCnf afterCnf certificate conflict)
    (fun _ids rest1 =>
      rest1
        (ay_prpl_ProofReconstruction beforeCnf afterCnf certificate conflict)
        (fun _parents rest2 =>
          rest2
            (ay_prpl_ProofReconstruction
              beforeCnf afterCnf certificate conflict)
            (fun _digest rest3 =>
              rest3
                (ay_prpl_ProofReconstruction
                  beforeCnf afterCnf certificate conflict)
                (fun _checker rest4 =>
                  rest4
                    (ay_prpl_ProofReconstruction
                      beforeCnf afterCnf certificate conflict)
                    (fun _eq rest5 =>
                      rest5
                        (ay_prpl_ProofReconstruction
                          beforeCnf afterCnf certificate conflict)
                        (fun _model rest6 =>
                          rest6
                            (ay_prpl_ProofReconstruction
                              beforeCnf afterCnf certificate conflict)
                            (fun proof _tail => proof)))))))

theorem ay_prpl_link_fingerprint
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop) :
    ay_prpl_AcceptedProofLink
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness ->
    ay_prpl_FingerprintLineage
      originalFingerprint preprocessedFingerprint lineageWitness := by
  intro accepted
  exact accepted
    (ay_prpl_FingerprintLineage
      originalFingerprint preprocessedFingerprint lineageWitness)
    (fun _ids rest1 =>
      rest1
        (ay_prpl_FingerprintLineage
          originalFingerprint preprocessedFingerprint lineageWitness)
        (fun _parents rest2 =>
          rest2
            (ay_prpl_FingerprintLineage
              originalFingerprint preprocessedFingerprint lineageWitness)
            (fun _digest rest3 =>
              rest3
                (ay_prpl_FingerprintLineage
                  originalFingerprint preprocessedFingerprint lineageWitness)
                (fun _checker rest4 =>
                  rest4
                    (ay_prpl_FingerprintLineage
                      originalFingerprint preprocessedFingerprint
                      lineageWitness)
                    (fun _eq rest5 =>
                      rest5
                        (ay_prpl_FingerprintLineage
                          originalFingerprint preprocessedFingerprint
                          lineageWitness)
                        (fun _model rest6 =>
                          rest6
                            (ay_prpl_FingerprintLineage
                              originalFingerprint preprocessedFingerprint
                              lineageWitness)
                            (fun _proof fp => fp)))))))

theorem ay_prpl_sat_pullback
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop) :
    ay_prpl_AcceptedProofLink
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness ->
    ay_prpl_Sat afterCnf afterModel ->
    ay_prpl_Sat beforeCnf beforeModel := by
  intro accepted afterSat
  exact
    (ay_prpl_link_model_reconstruction
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness accepted)
      afterSat

theorem ay_prpl_unsat_pushback
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop) :
    ay_prpl_AcceptedProofLink
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness ->
    ay_prpl_Replay afterCnf certificate conflict ->
    certificate ->
    beforeCnf ->
    conflict := by
  intro accepted replay cert before
  exact
    (ay_prpl_link_proof_reconstruction
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness accepted)
      replay cert before

theorem ay_prpl_public_sat
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop)
    (exitCode : Prop) :
    ay_prpl_AcceptedProofLink
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness ->
    ay_prpl_Sat afterCnf afterModel ->
    exitCode ->
    ay_prpl_PublicResult beforeCnf beforeModel certificate conflict exitCode := by
  intro accepted afterSat exit
  exact ay_prpl_disj_left
    (ay_prpl_ExitCodeSound exitCode (ay_prpl_Sat beforeCnf beforeModel))
    (ay_prpl_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))
    (ay_prpl_conj_intro exitCode
      (ay_prpl_Sat beforeCnf beforeModel)
      exit
      (ay_prpl_sat_pullback
        beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
        leftParent rightParent coveredParents coverageWitness proofLinkDigest
        manifestDigest proofLinkCertificate checkerAccepted afterModel
        beforeModel certificate conflict originalFingerprint
        preprocessedFingerprint lineageWitness accepted afterSat))

theorem ay_prpl_public_unsat
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedClauseId : Prop) (replayedClauseId : Prop)
    (stabilityWitness : Prop)
    (leftParent : Prop) (rightParent : Prop)
    (coveredParents : Prop) (coverageWitness : Prop)
    (proofLinkDigest : Prop) (manifestDigest : Prop)
    (proofLinkCertificate : Prop) (checkerAccepted : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (preprocessedFingerprint : Prop)
    (lineageWitness : Prop)
    (exitCode : Prop) :
    ay_prpl_AcceptedProofLink
      beforeCnf afterCnf emittedClauseId replayedClauseId stabilityWitness
      leftParent rightParent coveredParents coverageWitness proofLinkDigest
      manifestDigest proofLinkCertificate checkerAccepted afterModel
      beforeModel certificate conflict originalFingerprint
      preprocessedFingerprint lineageWitness ->
    ay_prpl_Replay afterCnf certificate conflict ->
    exitCode ->
    ay_prpl_PublicResult beforeCnf beforeModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_prpl_disj_right
    (ay_prpl_ExitCodeSound exitCode (ay_prpl_Sat beforeCnf beforeModel))
    (ay_prpl_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))
    (ay_prpl_conj_intro exitCode
      (certificate -> beforeCnf -> conflict)
      exit
      (fun cert before =>
        ay_prpl_unsat_pushback
          beforeCnf afterCnf emittedClauseId replayedClauseId
          stabilityWitness leftParent rightParent coveredParents
          coverageWitness proofLinkDigest manifestDigest proofLinkCertificate
          checkerAccepted afterModel beforeModel certificate conflict
          originalFingerprint preprocessedFingerprint lineageWitness accepted
          replay cert before))

theorem ay_prpl_failure_stale_clause_id
    (staleClauseId : Prop) (missingParentCoverage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (brokenReconstruction : Prop) (staleFingerprint : Prop) :
    staleClauseId ->
    ay_prpl_LinkFailure
      staleClauseId missingParentCoverage digestMismatch replayRejected
      brokenReconstruction staleFingerprint := by
  intro stale
  exact ay_prpl_disj_left staleClauseId
    (ay_prpl_Disj missingParentCoverage
      (ay_prpl_Disj digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint))))
    stale

theorem ay_prpl_failure_missing_parent_coverage
    (staleClauseId : Prop) (missingParentCoverage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (brokenReconstruction : Prop) (staleFingerprint : Prop) :
    missingParentCoverage ->
    ay_prpl_LinkFailure
      staleClauseId missingParentCoverage digestMismatch replayRejected
      brokenReconstruction staleFingerprint := by
  intro missing
  exact ay_prpl_disj_right staleClauseId
    (ay_prpl_Disj missingParentCoverage
      (ay_prpl_Disj digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint))))
    (ay_prpl_disj_left missingParentCoverage
      (ay_prpl_Disj digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint)))
      missing)

theorem ay_prpl_failure_digest_mismatch
    (staleClauseId : Prop) (missingParentCoverage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (brokenReconstruction : Prop) (staleFingerprint : Prop) :
    digestMismatch ->
    ay_prpl_LinkFailure
      staleClauseId missingParentCoverage digestMismatch replayRejected
      brokenReconstruction staleFingerprint := by
  intro mismatch
  exact ay_prpl_disj_right staleClauseId
    (ay_prpl_Disj missingParentCoverage
      (ay_prpl_Disj digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint))))
    (ay_prpl_disj_right missingParentCoverage
      (ay_prpl_Disj digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint)))
      (ay_prpl_disj_left digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint))
        mismatch))

theorem ay_prpl_failure_replay_rejected
    (staleClauseId : Prop) (missingParentCoverage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (brokenReconstruction : Prop) (staleFingerprint : Prop) :
    replayRejected ->
    ay_prpl_LinkFailure
      staleClauseId missingParentCoverage digestMismatch replayRejected
      brokenReconstruction staleFingerprint := by
  intro rejected
  exact ay_prpl_disj_right staleClauseId
    (ay_prpl_Disj missingParentCoverage
      (ay_prpl_Disj digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint))))
    (ay_prpl_disj_right missingParentCoverage
      (ay_prpl_Disj digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint)))
      (ay_prpl_disj_right digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint))
        (ay_prpl_disj_left replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint)
          rejected)))

theorem ay_prpl_failure_broken_reconstruction
    (staleClauseId : Prop) (missingParentCoverage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (brokenReconstruction : Prop) (staleFingerprint : Prop) :
    brokenReconstruction ->
    ay_prpl_LinkFailure
      staleClauseId missingParentCoverage digestMismatch replayRejected
      brokenReconstruction staleFingerprint := by
  intro broken
  exact ay_prpl_disj_right staleClauseId
    (ay_prpl_Disj missingParentCoverage
      (ay_prpl_Disj digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint))))
    (ay_prpl_disj_right missingParentCoverage
      (ay_prpl_Disj digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint)))
      (ay_prpl_disj_right digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint))
        (ay_prpl_disj_right replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint)
          (ay_prpl_disj_left brokenReconstruction staleFingerprint broken))))

theorem ay_prpl_failure_stale_fingerprint
    (staleClauseId : Prop) (missingParentCoverage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (brokenReconstruction : Prop) (staleFingerprint : Prop) :
    staleFingerprint ->
    ay_prpl_LinkFailure
      staleClauseId missingParentCoverage digestMismatch replayRejected
      brokenReconstruction staleFingerprint := by
  intro stale
  exact ay_prpl_disj_right staleClauseId
    (ay_prpl_Disj missingParentCoverage
      (ay_prpl_Disj digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint))))
    (ay_prpl_disj_right missingParentCoverage
      (ay_prpl_Disj digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint)))
      (ay_prpl_disj_right digestMismatch
        (ay_prpl_Disj replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint))
        (ay_prpl_disj_right replayRejected
          (ay_prpl_Disj brokenReconstruction staleFingerprint)
          (ay_prpl_disj_right brokenReconstruction staleFingerprint stale))))

theorem ay_prpl_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleClauseId : Prop) (missingParentCoverage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (brokenReconstruction : Prop) (staleFingerprint : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_prpl_DiagnosticProofLinkLogEntry
      previousLog nextLog currentCnf staleClauseId missingParentCoverage
      digestMismatch replayRejected brokenReconstruction staleFingerprint
      recompute diagnostic ->
    ay_prpl_LinkFailure
      staleClauseId missingParentCoverage digestMismatch replayRejected
      brokenReconstruction staleFingerprint := by
  intro entry
  exact entry
    (ay_prpl_LinkFailure
      staleClauseId missingParentCoverage digestMismatch replayRejected
      brokenReconstruction staleFingerprint)
    (fun _previous rest1 =>
      rest1
        (ay_prpl_LinkFailure
          staleClauseId missingParentCoverage digestMismatch replayRejected
          brokenReconstruction staleFingerprint)
        (fun body _next =>
          body
            (ay_prpl_LinkFailure
              staleClauseId missingParentCoverage digestMismatch replayRejected
              brokenReconstruction staleFingerprint)
            (fun failure _tail => failure)))

theorem ay_prpl_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleClauseId : Prop) (missingParentCoverage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (brokenReconstruction : Prop) (staleFingerprint : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_prpl_DiagnosticProofLinkLogEntry
      previousLog nextLog currentCnf staleClauseId missingParentCoverage
      digestMismatch replayRejected brokenReconstruction staleFingerprint
      recompute diagnostic ->
    ay_prpl_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_prpl_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_prpl_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_prpl_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_prpl_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_prpl_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (staleClauseId : Prop) (missingParentCoverage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (brokenReconstruction : Prop) (staleFingerprint : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_prpl_DiagnosticProofLinkLogEntry
      previousLog nextLog currentCnf staleClauseId missingParentCoverage
      digestMismatch replayRejected brokenReconstruction staleFingerprint
      recompute diagnostic ->
    ay_prpl_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_prpl_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_prpl_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_prpl_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_prpl_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_prpl_failure_no_claim
    (staleClauseId : Prop) (missingParentCoverage : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (brokenReconstruction : Prop) (staleFingerprint : Prop)
    (diagnostic : Prop) :
    ay_prpl_LinkFailure
      staleClauseId missingParentCoverage digestMismatch replayRejected
      brokenReconstruction staleFingerprint ->
    diagnostic ->
    ay_prpl_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
