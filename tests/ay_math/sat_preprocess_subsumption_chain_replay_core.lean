-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Subsumption-chain replay soundness for preprocessing. The propositions
-- stand for subsuming clause IDs, parent coverage, deletion/retention lineage,
-- model/proof reconstruction hooks, digest membership, checker replay,
-- original-instance fingerprint agreement, diagnostics, and public SAT/UNSAT
-- reports.

def ay_pscr_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pscr_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pscr_Equisat (before : Prop) (after : Prop) :=
  ay_pscr_Conj (before -> after) (after -> before)

def ay_pscr_Sat (cnf : Prop) (model : Prop) :=
  ay_pscr_Conj cnf model

def ay_pscr_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pscr_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pscr_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pscr_SubsumingClauseIds
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop) :=
  ay_pscr_Conj idWitness
    (ay_pscr_IdMatch emittedSubsumerIds replayedSubsumerIds)

def ay_pscr_ParentCoverage
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop) :=
  ay_pscr_Conj coverageWitness
    (subsumingParents -> coveredParents)

def ay_pscr_DeletionRetentionLineage
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop) :=
  ay_pscr_Conj lineageWitness
    (ay_pscr_Conj deletedClauses retainedClauses)

def ay_pscr_ModelReconstruction
    (afterCnf : Prop) (beforeCnf : Prop)
    (afterModel : Prop) (beforeModel : Prop) :=
  ay_pscr_Sat afterCnf afterModel ->
    ay_pscr_Sat beforeCnf beforeModel

def ay_pscr_ProofReconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pscr_Replay afterCnf certificate conflict ->
    certificate -> beforeCnf -> conflict

def ay_pscr_DigestMembership
    (chainDigest : Prop) (manifestDigest : Prop) :=
  ay_pscr_Conj chainDigest manifestDigest

def ay_pscr_CheckerReplay
    (chainCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pscr_Conj chainCertificate checkerAccepted

def ay_pscr_FingerprintAgreement
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pscr_Conj fingerprintWitness
    (ay_pscr_IdMatch originalFingerprint replayFingerprint)

def ay_pscr_AcceptedSubsumptionChain
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pscr_Conj
    (ay_pscr_SubsumingClauseIds
      emittedSubsumerIds replayedSubsumerIds idWitness)
    (ay_pscr_Conj
      (ay_pscr_ParentCoverage
        subsumingParents coveredParents coverageWitness)
      (ay_pscr_Conj
        (ay_pscr_DeletionRetentionLineage
          deletedClauses retainedClauses lineageWitness)
        (ay_pscr_Conj
          (ay_pscr_Equisat beforeCnf afterCnf)
          (ay_pscr_Conj
            (ay_pscr_ModelReconstruction
              afterCnf beforeCnf afterModel beforeModel)
            (ay_pscr_Conj
              (ay_pscr_ProofReconstruction
                beforeCnf afterCnf certificate conflict)
              (ay_pscr_Conj
                (ay_pscr_DigestMembership chainDigest manifestDigest)
                (ay_pscr_Conj
                  (ay_pscr_CheckerReplay
                    chainCertificate checkerAccepted)
                  (ay_pscr_FingerprintAgreement
                    originalFingerprint replayFingerprint
                    fingerprintWitness))))))))

def ay_pscr_AcceptedChainLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pscr_Conj previousLog
    (ay_pscr_Conj
      (ay_pscr_AcceptedSubsumptionChain
        beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds
        idWitness subsumingParents coveredParents coverageWitness
        deletedClauses retainedClauses lineageWitness afterModel beforeModel
        certificate conflict chainDigest manifestDigest chainCertificate
        checkerAccepted originalFingerprint replayFingerprint
        fingerprintWitness)
      nextLog)

def ay_pscr_ChainFailure
    (missingParentCoverage : Prop) (staleSubsumerIds : Prop)
    (unretainedDeletedClauses : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :=
  ay_pscr_Disj missingParentCoverage
    (ay_pscr_Disj staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)))))

def ay_pscr_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pscr_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pscr_Conj currentCnf recompute

def ay_pscr_DiagnosticChainLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingParentCoverage : Prop) (staleSubsumerIds : Prop)
    (unretainedDeletedClauses : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pscr_Conj previousLog
    (ay_pscr_Conj
      (ay_pscr_Conj
        (ay_pscr_ChainFailure
          missingParentCoverage staleSubsumerIds unretainedDeletedClauses
          brokenReconstruction digestMismatch replayRejected
          fingerprintDrift)
        (ay_pscr_Conj
          (ay_pscr_RecomputeObligation currentCnf recompute)
          (ay_pscr_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pscr_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pscr_Conj exitCode claim

def ay_pscr_PublicResult
    (beforeCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pscr_Disj
    (ay_pscr_ExitCodeSound exitCode (ay_pscr_Sat beforeCnf model))
    (ay_pscr_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))

theorem ay_pscr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pscr_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pscr_conj_left
    (left : Prop) (right : Prop) :
    ay_pscr_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pscr_conj_right
    (left : Prop) (right : Prop) :
    ay_pscr_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pscr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pscr_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pscr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pscr_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pscr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pscr_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pscr_conj_left (before -> after) (after -> before) eq

theorem ay_pscr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pscr_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pscr_conj_right (before -> after) (after -> before) eq

theorem ay_pscr_chain_subsumer_ids
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pscr_AcceptedSubsumptionChain
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness ->
    ay_pscr_SubsumingClauseIds
      emittedSubsumerIds replayedSubsumerIds idWitness := by
  intro accepted
  exact ay_pscr_conj_left
    (ay_pscr_SubsumingClauseIds
      emittedSubsumerIds replayedSubsumerIds idWitness)
    (ay_pscr_Conj
      (ay_pscr_ParentCoverage
        subsumingParents coveredParents coverageWitness)
      (ay_pscr_Conj
        (ay_pscr_DeletionRetentionLineage
          deletedClauses retainedClauses lineageWitness)
        (ay_pscr_Conj
          (ay_pscr_Equisat beforeCnf afterCnf)
          (ay_pscr_Conj
            (ay_pscr_ModelReconstruction
              afterCnf beforeCnf afterModel beforeModel)
            (ay_pscr_Conj
              (ay_pscr_ProofReconstruction
                beforeCnf afterCnf certificate conflict)
              (ay_pscr_Conj
                (ay_pscr_DigestMembership chainDigest manifestDigest)
                (ay_pscr_Conj
                  (ay_pscr_CheckerReplay
                    chainCertificate checkerAccepted)
                  (ay_pscr_FingerprintAgreement
                    originalFingerprint replayFingerprint
                    fingerprintWitness))))))))
    accepted

theorem ay_pscr_chain_parent_coverage
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pscr_AcceptedSubsumptionChain
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness ->
    ay_pscr_ParentCoverage subsumingParents coveredParents coverageWitness := by
  intro accepted
  exact accepted
    (ay_pscr_ParentCoverage subsumingParents coveredParents coverageWitness)
    (fun _ids rest1 =>
      rest1
        (ay_pscr_ParentCoverage subsumingParents coveredParents coverageWitness)
        (fun coverage _tail => coverage))

theorem ay_pscr_chain_deletion_retention
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pscr_AcceptedSubsumptionChain
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness ->
    ay_pscr_DeletionRetentionLineage
      deletedClauses retainedClauses lineageWitness := by
  intro accepted
  exact accepted
    (ay_pscr_DeletionRetentionLineage
      deletedClauses retainedClauses lineageWitness)
    (fun _ids rest1 =>
      rest1
        (ay_pscr_DeletionRetentionLineage
          deletedClauses retainedClauses lineageWitness)
        (fun _coverage rest2 =>
          rest2
            (ay_pscr_DeletionRetentionLineage
              deletedClauses retainedClauses lineageWitness)
            (fun lineage _tail => lineage)))

theorem ay_pscr_chain_equisat
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pscr_AcceptedSubsumptionChain
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness ->
    ay_pscr_Equisat beforeCnf afterCnf := by
  intro accepted
  exact accepted
    (ay_pscr_Equisat beforeCnf afterCnf)
    (fun _ids rest1 =>
      rest1
        (ay_pscr_Equisat beforeCnf afterCnf)
        (fun _coverage rest2 =>
          rest2
            (ay_pscr_Equisat beforeCnf afterCnf)
            (fun _lineage rest3 =>
              rest3
                (ay_pscr_Equisat beforeCnf afterCnf)
                (fun eq _tail => eq))))

theorem ay_pscr_chain_model_reconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pscr_AcceptedSubsumptionChain
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness ->
    ay_pscr_ModelReconstruction afterCnf beforeCnf afterModel beforeModel := by
  intro accepted
  exact accepted
    (ay_pscr_ModelReconstruction afterCnf beforeCnf afterModel beforeModel)
    (fun _ids rest1 =>
      rest1
        (ay_pscr_ModelReconstruction afterCnf beforeCnf afterModel beforeModel)
        (fun _coverage rest2 =>
          rest2
            (ay_pscr_ModelReconstruction
              afterCnf beforeCnf afterModel beforeModel)
            (fun _lineage rest3 =>
              rest3
                (ay_pscr_ModelReconstruction
                  afterCnf beforeCnf afterModel beforeModel)
                (fun _eq rest4 =>
                  rest4
                    (ay_pscr_ModelReconstruction
                      afterCnf beforeCnf afterModel beforeModel)
                    (fun model _tail => model)))))

theorem ay_pscr_chain_proof_reconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pscr_AcceptedSubsumptionChain
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness ->
    ay_pscr_ProofReconstruction beforeCnf afterCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_pscr_ProofReconstruction beforeCnf afterCnf certificate conflict)
    (fun _ids rest1 =>
      rest1
        (ay_pscr_ProofReconstruction beforeCnf afterCnf certificate conflict)
        (fun _coverage rest2 =>
          rest2
            (ay_pscr_ProofReconstruction
              beforeCnf afterCnf certificate conflict)
            (fun _lineage rest3 =>
              rest3
                (ay_pscr_ProofReconstruction
                  beforeCnf afterCnf certificate conflict)
                (fun _eq rest4 =>
                  rest4
                    (ay_pscr_ProofReconstruction
                      beforeCnf afterCnf certificate conflict)
                    (fun _model rest5 =>
                      rest5
                        (ay_pscr_ProofReconstruction
                          beforeCnf afterCnf certificate conflict)
                        (fun proof _tail => proof))))))

theorem ay_pscr_chain_digest
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pscr_AcceptedSubsumptionChain
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness ->
    ay_pscr_DigestMembership chainDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_pscr_DigestMembership chainDigest manifestDigest)
    (fun _ids rest1 =>
      rest1
        (ay_pscr_DigestMembership chainDigest manifestDigest)
        (fun _coverage rest2 =>
          rest2
            (ay_pscr_DigestMembership chainDigest manifestDigest)
            (fun _lineage rest3 =>
              rest3
                (ay_pscr_DigestMembership chainDigest manifestDigest)
                (fun _eq rest4 =>
                  rest4
                    (ay_pscr_DigestMembership chainDigest manifestDigest)
                    (fun _model rest5 =>
                      rest5
                        (ay_pscr_DigestMembership chainDigest manifestDigest)
                        (fun _proof rest6 =>
                          rest6
                            (ay_pscr_DigestMembership chainDigest manifestDigest)
                            (fun digest _tail => digest)))))))

theorem ay_pscr_chain_checker
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pscr_AcceptedSubsumptionChain
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness ->
    ay_pscr_CheckerReplay chainCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pscr_CheckerReplay chainCertificate checkerAccepted)
    (fun _ids rest1 =>
      rest1
        (ay_pscr_CheckerReplay chainCertificate checkerAccepted)
        (fun _coverage rest2 =>
          rest2
            (ay_pscr_CheckerReplay chainCertificate checkerAccepted)
            (fun _lineage rest3 =>
              rest3
                (ay_pscr_CheckerReplay chainCertificate checkerAccepted)
                (fun _eq rest4 =>
                  rest4
                    (ay_pscr_CheckerReplay chainCertificate checkerAccepted)
                    (fun _model rest5 =>
                      rest5
                        (ay_pscr_CheckerReplay
                          chainCertificate checkerAccepted)
                        (fun _proof rest6 =>
                          rest6
                            (ay_pscr_CheckerReplay
                              chainCertificate checkerAccepted)
                            (fun _digest rest7 =>
                              rest7
                                (ay_pscr_CheckerReplay
                                  chainCertificate checkerAccepted)
                                (fun checker _tail => checker))))))))

theorem ay_pscr_chain_fingerprint
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pscr_AcceptedSubsumptionChain
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness ->
    ay_pscr_FingerprintAgreement
      originalFingerprint replayFingerprint fingerprintWitness := by
  intro accepted
  exact accepted
    (ay_pscr_FingerprintAgreement
      originalFingerprint replayFingerprint fingerprintWitness)
    (fun _ids rest1 =>
      rest1
        (ay_pscr_FingerprintAgreement
          originalFingerprint replayFingerprint fingerprintWitness)
        (fun _coverage rest2 =>
          rest2
            (ay_pscr_FingerprintAgreement
              originalFingerprint replayFingerprint fingerprintWitness)
            (fun _lineage rest3 =>
              rest3
                (ay_pscr_FingerprintAgreement
                  originalFingerprint replayFingerprint fingerprintWitness)
                (fun _eq rest4 =>
                  rest4
                    (ay_pscr_FingerprintAgreement
                      originalFingerprint replayFingerprint fingerprintWitness)
                    (fun _model rest5 =>
                      rest5
                        (ay_pscr_FingerprintAgreement
                          originalFingerprint replayFingerprint
                          fingerprintWitness)
                        (fun _proof rest6 =>
                          rest6
                            (ay_pscr_FingerprintAgreement
                              originalFingerprint replayFingerprint
                              fingerprintWitness)
                            (fun _digest rest7 =>
                              rest7
                                (ay_pscr_FingerprintAgreement
                                  originalFingerprint replayFingerprint
                                  fingerprintWitness)
                                (fun _checker fp => fp))))))))

theorem ay_pscr_sat_pullback
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pscr_AcceptedSubsumptionChain
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness ->
    ay_pscr_Sat afterCnf afterModel ->
    ay_pscr_Sat beforeCnf beforeModel := by
  intro accepted afterSat
  exact
    (ay_pscr_chain_model_reconstruction
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness accepted)
      afterSat

theorem ay_pscr_unsat_pushback
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pscr_AcceptedSubsumptionChain
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness ->
    ay_pscr_Replay afterCnf certificate conflict ->
    certificate ->
    beforeCnf ->
    conflict := by
  intro accepted replay cert before
  exact
    (ay_pscr_chain_proof_reconstruction
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness accepted)
      replay cert before

theorem ay_pscr_public_sat
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pscr_AcceptedSubsumptionChain
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness ->
    ay_pscr_Sat afterCnf afterModel ->
    exitCode ->
    ay_pscr_PublicResult beforeCnf beforeModel certificate conflict exitCode := by
  intro accepted afterSat exit
  exact ay_pscr_disj_left
    (ay_pscr_ExitCodeSound exitCode (ay_pscr_Sat beforeCnf beforeModel))
    (ay_pscr_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))
    (ay_pscr_conj_intro exitCode
      (ay_pscr_Sat beforeCnf beforeModel)
      exit
      (ay_pscr_sat_pullback
        beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
        subsumingParents coveredParents coverageWitness deletedClauses
        retainedClauses lineageWitness afterModel beforeModel certificate
        conflict chainDigest manifestDigest chainCertificate checkerAccepted
        originalFingerprint replayFingerprint fingerprintWitness accepted
        afterSat))

theorem ay_pscr_public_unsat
    (beforeCnf : Prop) (afterCnf : Prop)
    (emittedSubsumerIds : Prop) (replayedSubsumerIds : Prop)
    (idWitness : Prop)
    (subsumingParents : Prop) (coveredParents : Prop)
    (coverageWitness : Prop)
    (deletedClauses : Prop) (retainedClauses : Prop)
    (lineageWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (chainDigest : Prop) (manifestDigest : Prop)
    (chainCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (replayFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pscr_AcceptedSubsumptionChain
      beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
      subsumingParents coveredParents coverageWitness deletedClauses
      retainedClauses lineageWitness afterModel beforeModel certificate
      conflict chainDigest manifestDigest chainCertificate checkerAccepted
      originalFingerprint replayFingerprint fingerprintWitness ->
    ay_pscr_Replay afterCnf certificate conflict ->
    exitCode ->
    ay_pscr_PublicResult beforeCnf beforeModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_pscr_disj_right
    (ay_pscr_ExitCodeSound exitCode (ay_pscr_Sat beforeCnf beforeModel))
    (ay_pscr_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))
    (ay_pscr_conj_intro exitCode
      (certificate -> beforeCnf -> conflict)
      exit
      (fun cert before =>
        ay_pscr_unsat_pushback
          beforeCnf afterCnf emittedSubsumerIds replayedSubsumerIds idWitness
          subsumingParents coveredParents coverageWitness deletedClauses
          retainedClauses lineageWitness afterModel beforeModel certificate
          conflict chainDigest manifestDigest chainCertificate checkerAccepted
          originalFingerprint replayFingerprint fingerprintWitness accepted replay
          cert before))

theorem ay_pscr_failure_missing_parent_coverage
    (missingParentCoverage : Prop) (staleSubsumerIds : Prop)
    (unretainedDeletedClauses : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    missingParentCoverage ->
    ay_pscr_ChainFailure
      missingParentCoverage staleSubsumerIds unretainedDeletedClauses
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro missing
  exact ay_pscr_disj_left missingParentCoverage
    (ay_pscr_Disj staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)))))
    missing

theorem ay_pscr_failure_stale_subsumer_ids
    (missingParentCoverage : Prop) (staleSubsumerIds : Prop)
    (unretainedDeletedClauses : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    staleSubsumerIds ->
    ay_pscr_ChainFailure
      missingParentCoverage staleSubsumerIds unretainedDeletedClauses
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro stale
  exact ay_pscr_disj_right missingParentCoverage
    (ay_pscr_Disj staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)))))
    (ay_pscr_disj_left staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift))))
      stale)

theorem ay_pscr_failure_unretained_deleted_clauses
    (missingParentCoverage : Prop) (staleSubsumerIds : Prop)
    (unretainedDeletedClauses : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    unretainedDeletedClauses ->
    ay_pscr_ChainFailure
      missingParentCoverage staleSubsumerIds unretainedDeletedClauses
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro unretained
  exact ay_pscr_disj_right missingParentCoverage
    (ay_pscr_Disj staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)))))
    (ay_pscr_disj_right staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift))))
      (ay_pscr_disj_left unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)))
        unretained))

theorem ay_pscr_failure_broken_reconstruction
    (missingParentCoverage : Prop) (staleSubsumerIds : Prop)
    (unretainedDeletedClauses : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    brokenReconstruction ->
    ay_pscr_ChainFailure
      missingParentCoverage staleSubsumerIds unretainedDeletedClauses
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro broken
  exact ay_pscr_disj_right missingParentCoverage
    (ay_pscr_Disj staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)))))
    (ay_pscr_disj_right staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift))))
      (ay_pscr_disj_right unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)))
        (ay_pscr_disj_left brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift))
          broken)))

theorem ay_pscr_failure_digest_mismatch
    (missingParentCoverage : Prop) (staleSubsumerIds : Prop)
    (unretainedDeletedClauses : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    digestMismatch ->
    ay_pscr_ChainFailure
      missingParentCoverage staleSubsumerIds unretainedDeletedClauses
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro mismatch
  exact ay_pscr_disj_right missingParentCoverage
    (ay_pscr_Disj staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)))))
    (ay_pscr_disj_right staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift))))
      (ay_pscr_disj_right unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)))
        (ay_pscr_disj_right brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift))
          (ay_pscr_disj_left digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)
            mismatch))))

theorem ay_pscr_failure_replay_rejected
    (missingParentCoverage : Prop) (staleSubsumerIds : Prop)
    (unretainedDeletedClauses : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    replayRejected ->
    ay_pscr_ChainFailure
      missingParentCoverage staleSubsumerIds unretainedDeletedClauses
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro rejected
  exact ay_pscr_disj_right missingParentCoverage
    (ay_pscr_Disj staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)))))
    (ay_pscr_disj_right staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift))))
      (ay_pscr_disj_right unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)))
        (ay_pscr_disj_right brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift))
          (ay_pscr_disj_right digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)
            (ay_pscr_disj_left replayRejected fingerprintDrift rejected)))))

theorem ay_pscr_failure_fingerprint_drift
    (missingParentCoverage : Prop) (staleSubsumerIds : Prop)
    (unretainedDeletedClauses : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    fingerprintDrift ->
    ay_pscr_ChainFailure
      missingParentCoverage staleSubsumerIds unretainedDeletedClauses
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro drift
  exact ay_pscr_disj_right missingParentCoverage
    (ay_pscr_Disj staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)))))
    (ay_pscr_disj_right staleSubsumerIds
      (ay_pscr_Disj unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift))))
      (ay_pscr_disj_right unretainedDeletedClauses
        (ay_pscr_Disj brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)))
        (ay_pscr_disj_right brokenReconstruction
          (ay_pscr_Disj digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift))
          (ay_pscr_disj_right digestMismatch
            (ay_pscr_Disj replayRejected fingerprintDrift)
            (ay_pscr_disj_right replayRejected fingerprintDrift drift)))))

theorem ay_pscr_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingParentCoverage : Prop) (staleSubsumerIds : Prop)
    (unretainedDeletedClauses : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pscr_DiagnosticChainLogEntry
      previousLog nextLog currentCnf missingParentCoverage staleSubsumerIds
      unretainedDeletedClauses brokenReconstruction digestMismatch
      replayRejected fingerprintDrift recompute diagnostic ->
    ay_pscr_ChainFailure
      missingParentCoverage staleSubsumerIds unretainedDeletedClauses
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro entry
  exact entry
    (ay_pscr_ChainFailure
      missingParentCoverage staleSubsumerIds unretainedDeletedClauses
      brokenReconstruction digestMismatch replayRejected fingerprintDrift)
    (fun _previous rest1 =>
      rest1
        (ay_pscr_ChainFailure
          missingParentCoverage staleSubsumerIds unretainedDeletedClauses
          brokenReconstruction digestMismatch replayRejected fingerprintDrift)
        (fun body _next =>
          body
            (ay_pscr_ChainFailure
              missingParentCoverage staleSubsumerIds unretainedDeletedClauses
              brokenReconstruction digestMismatch replayRejected
              fingerprintDrift)
            (fun failure _tail => failure)))

theorem ay_pscr_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingParentCoverage : Prop) (staleSubsumerIds : Prop)
    (unretainedDeletedClauses : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pscr_DiagnosticChainLogEntry
      previousLog nextLog currentCnf missingParentCoverage staleSubsumerIds
      unretainedDeletedClauses brokenReconstruction digestMismatch
      replayRejected fingerprintDrift recompute diagnostic ->
    ay_pscr_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_pscr_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_pscr_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_pscr_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_pscr_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_pscr_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingParentCoverage : Prop) (staleSubsumerIds : Prop)
    (unretainedDeletedClauses : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pscr_DiagnosticChainLogEntry
      previousLog nextLog currentCnf missingParentCoverage staleSubsumerIds
      unretainedDeletedClauses brokenReconstruction digestMismatch
      replayRejected fingerprintDrift recompute diagnostic ->
    ay_pscr_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_pscr_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_pscr_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_pscr_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_pscr_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_pscr_failure_no_claim
    (missingParentCoverage : Prop) (staleSubsumerIds : Prop)
    (unretainedDeletedClauses : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (diagnostic : Prop) :
    ay_pscr_ChainFailure
      missingParentCoverage staleSubsumerIds unretainedDeletedClauses
      brokenReconstruction digestMismatch replayRejected fingerprintDrift ->
    diagnostic ->
    ay_pscr_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
