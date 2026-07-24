-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause subsumption and self-subsuming-resolution certificate soundness for
-- preprocessing. The propositions stand for clause-removal/strengthening
-- witnesses, formula fingerprint lineage, reconstruction maps, digest
-- membership, checker replay, diagnostics, and public SAT/UNSAT reports.

def ay_pcsc_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pcsc_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pcsc_Equisat (before : Prop) (after : Prop) :=
  ay_pcsc_Conj (before -> after) (after -> before)

def ay_pcsc_Sat (cnf : Prop) (model : Prop) :=
  ay_pcsc_Conj cnf model

def ay_pcsc_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pcsc_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pcsc_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pcsc_SubsumptionWitness
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (witness : Prop) :=
  ay_pcsc_Conj witness
    (ay_pcsc_Conj clauseId (keptClause -> removedClause))

def ay_pcsc_ResolutionWitness
    (sourceClause : Prop) (strengthenedClause : Prop)
    (pivotLiteral : Prop) (witness : Prop) :=
  ay_pcsc_Conj witness
    (ay_pcsc_Conj pivotLiteral (sourceClause -> strengthenedClause))

def ay_pcsc_ModelReconstruction
    (afterCnf : Prop) (beforeCnf : Prop)
    (afterModel : Prop) (beforeModel : Prop) :=
  ay_pcsc_Sat afterCnf afterModel ->
    ay_pcsc_Sat beforeCnf beforeModel

def ay_pcsc_ProofReconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pcsc_Replay afterCnf certificate conflict ->
    certificate -> beforeCnf -> conflict

def ay_pcsc_FingerprintLineage
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop) :=
  ay_pcsc_Conj lineageWitness
    (ay_pcsc_IdMatch beforeFingerprint afterFingerprint)

def ay_pcsc_DigestMembership
    (stepDigest : Prop) (manifestDigest : Prop) :=
  ay_pcsc_Conj stepDigest manifestDigest

def ay_pcsc_CheckerReplay
    (certificateBundle : Prop) (checkerAccepted : Prop) :=
  ay_pcsc_Conj certificateBundle checkerAccepted

def ay_pcsc_ClauseSubsumptionCertificate
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :=
  ay_pcsc_Conj
    (ay_pcsc_SubsumptionWitness
      removedClause keptClause clauseId subsumptionWitness)
    (ay_pcsc_Conj
      (ay_pcsc_ResolutionWitness
        sourceClause strengthenedClause pivotLiteral resolutionWitness)
      (ay_pcsc_Conj
        (ay_pcsc_Equisat beforeCnf afterCnf)
        (ay_pcsc_Conj
          (ay_pcsc_ModelReconstruction
            afterCnf beforeCnf afterModel beforeModel)
          (ay_pcsc_Conj
            (ay_pcsc_ProofReconstruction
              beforeCnf afterCnf certificate conflict)
            (ay_pcsc_Conj
              (ay_pcsc_FingerprintLineage
                beforeFingerprint afterFingerprint lineageWitness)
              (ay_pcsc_Conj
                (ay_pcsc_DigestMembership stepDigest manifestDigest)
                (ay_pcsc_CheckerReplay
                  certificateBundle checkerAccepted)))))))

def ay_pcsc_AcceptedCertificateLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :=
  ay_pcsc_Conj previousLog
    (ay_pcsc_Conj
      (ay_pcsc_ClauseSubsumptionCertificate
        beforeCnf afterCnf removedClause keptClause clauseId
        subsumptionWitness sourceClause strengthenedClause pivotLiteral
        resolutionWitness afterModel beforeModel certificate conflict
        beforeFingerprint afterFingerprint lineageWitness stepDigest
        manifestDigest certificateBundle checkerAccepted)
      nextLog)

def ay_pcsc_CertificateFailure
    (missingWitness : Prop) (staleClauseId : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :=
  ay_pcsc_Disj missingWitness
    (ay_pcsc_Disj staleClauseId
      (ay_pcsc_Disj fingerprintMismatch
        (ay_pcsc_Disj digestMismatch replayRejected)))

def ay_pcsc_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pcsc_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pcsc_Conj currentCnf recompute

def ay_pcsc_DiagnosticCertificateLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingWitness : Prop) (staleClauseId : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pcsc_Conj previousLog
    (ay_pcsc_Conj
      (ay_pcsc_Conj
        (ay_pcsc_CertificateFailure
          missingWitness staleClauseId fingerprintMismatch digestMismatch
          replayRejected)
        (ay_pcsc_Conj
          (ay_pcsc_RecomputeObligation currentCnf recompute)
          (ay_pcsc_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pcsc_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pcsc_Conj exitCode claim

def ay_pcsc_PublicResult
    (beforeCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pcsc_Disj
    (ay_pcsc_ExitCodeSound exitCode (ay_pcsc_Sat beforeCnf model))
    (ay_pcsc_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))

theorem ay_pcsc_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pcsc_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pcsc_conj_left
    (left : Prop) (right : Prop) :
    ay_pcsc_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pcsc_conj_right
    (left : Prop) (right : Prop) :
    ay_pcsc_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pcsc_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pcsc_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pcsc_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pcsc_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pcsc_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pcsc_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pcsc_conj_left (before -> after) (after -> before) eq

theorem ay_pcsc_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pcsc_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pcsc_conj_right (before -> after) (after -> before) eq

theorem ay_pcsc_certificate_subsumption
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_pcsc_ClauseSubsumptionCertificate
      beforeCnf afterCnf removedClause keptClause clauseId
      subsumptionWitness sourceClause strengthenedClause pivotLiteral
      resolutionWitness afterModel beforeModel certificate conflict
      beforeFingerprint afterFingerprint lineageWitness stepDigest
      manifestDigest certificateBundle checkerAccepted ->
    ay_pcsc_SubsumptionWitness
      removedClause keptClause clauseId subsumptionWitness := by
  intro accepted
  exact ay_pcsc_conj_left
    (ay_pcsc_SubsumptionWitness
      removedClause keptClause clauseId subsumptionWitness)
    (ay_pcsc_Conj
      (ay_pcsc_ResolutionWitness
        sourceClause strengthenedClause pivotLiteral resolutionWitness)
      (ay_pcsc_Conj
        (ay_pcsc_Equisat beforeCnf afterCnf)
        (ay_pcsc_Conj
          (ay_pcsc_ModelReconstruction
            afterCnf beforeCnf afterModel beforeModel)
          (ay_pcsc_Conj
            (ay_pcsc_ProofReconstruction
              beforeCnf afterCnf certificate conflict)
            (ay_pcsc_Conj
              (ay_pcsc_FingerprintLineage
                beforeFingerprint afterFingerprint lineageWitness)
              (ay_pcsc_Conj
                (ay_pcsc_DigestMembership stepDigest manifestDigest)
                (ay_pcsc_CheckerReplay
                  certificateBundle checkerAccepted)))))))
    accepted

theorem ay_pcsc_certificate_resolution
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_pcsc_ClauseSubsumptionCertificate
      beforeCnf afterCnf removedClause keptClause clauseId
      subsumptionWitness sourceClause strengthenedClause pivotLiteral
      resolutionWitness afterModel beforeModel certificate conflict
      beforeFingerprint afterFingerprint lineageWitness stepDigest
      manifestDigest certificateBundle checkerAccepted ->
    ay_pcsc_ResolutionWitness
      sourceClause strengthenedClause pivotLiteral resolutionWitness := by
  intro accepted
  exact accepted
    (ay_pcsc_ResolutionWitness
      sourceClause strengthenedClause pivotLiteral resolutionWitness)
    (fun _sub rest1 =>
      rest1
        (ay_pcsc_ResolutionWitness
          sourceClause strengthenedClause pivotLiteral resolutionWitness)
        (fun res _tail => res))

theorem ay_pcsc_certificate_equisat
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_pcsc_ClauseSubsumptionCertificate
      beforeCnf afterCnf removedClause keptClause clauseId
      subsumptionWitness sourceClause strengthenedClause pivotLiteral
      resolutionWitness afterModel beforeModel certificate conflict
      beforeFingerprint afterFingerprint lineageWitness stepDigest
      manifestDigest certificateBundle checkerAccepted ->
    ay_pcsc_Equisat beforeCnf afterCnf := by
  intro accepted
  exact accepted
    (ay_pcsc_Equisat beforeCnf afterCnf)
    (fun _sub rest1 =>
      rest1
        (ay_pcsc_Equisat beforeCnf afterCnf)
        (fun _res rest2 =>
          rest2
            (ay_pcsc_Equisat beforeCnf afterCnf)
            (fun eq _tail => eq)))

theorem ay_pcsc_certificate_model_reconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_pcsc_ClauseSubsumptionCertificate
      beforeCnf afterCnf removedClause keptClause clauseId
      subsumptionWitness sourceClause strengthenedClause pivotLiteral
      resolutionWitness afterModel beforeModel certificate conflict
      beforeFingerprint afterFingerprint lineageWitness stepDigest
      manifestDigest certificateBundle checkerAccepted ->
    ay_pcsc_ModelReconstruction afterCnf beforeCnf afterModel beforeModel := by
  intro accepted
  exact accepted
    (ay_pcsc_ModelReconstruction afterCnf beforeCnf afterModel beforeModel)
    (fun _sub rest1 =>
      rest1
        (ay_pcsc_ModelReconstruction afterCnf beforeCnf afterModel beforeModel)
        (fun _res rest2 =>
          rest2
            (ay_pcsc_ModelReconstruction
              afterCnf beforeCnf afterModel beforeModel)
            (fun _eq rest3 =>
              rest3
                (ay_pcsc_ModelReconstruction
                  afterCnf beforeCnf afterModel beforeModel)
                (fun model _tail => model))))

theorem ay_pcsc_certificate_proof_reconstruction
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_pcsc_ClauseSubsumptionCertificate
      beforeCnf afterCnf removedClause keptClause clauseId
      subsumptionWitness sourceClause strengthenedClause pivotLiteral
      resolutionWitness afterModel beforeModel certificate conflict
      beforeFingerprint afterFingerprint lineageWitness stepDigest
      manifestDigest certificateBundle checkerAccepted ->
    ay_pcsc_ProofReconstruction beforeCnf afterCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_pcsc_ProofReconstruction beforeCnf afterCnf certificate conflict)
    (fun _sub rest1 =>
      rest1
        (ay_pcsc_ProofReconstruction beforeCnf afterCnf certificate conflict)
        (fun _res rest2 =>
          rest2
            (ay_pcsc_ProofReconstruction beforeCnf afterCnf certificate conflict)
            (fun _eq rest3 =>
              rest3
                (ay_pcsc_ProofReconstruction
                  beforeCnf afterCnf certificate conflict)
                (fun _model rest4 =>
                  rest4
                    (ay_pcsc_ProofReconstruction
                      beforeCnf afterCnf certificate conflict)
                    (fun proof _tail => proof)))))

theorem ay_pcsc_certificate_fingerprint
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_pcsc_ClauseSubsumptionCertificate
      beforeCnf afterCnf removedClause keptClause clauseId
      subsumptionWitness sourceClause strengthenedClause pivotLiteral
      resolutionWitness afterModel beforeModel certificate conflict
      beforeFingerprint afterFingerprint lineageWitness stepDigest
      manifestDigest certificateBundle checkerAccepted ->
    ay_pcsc_FingerprintLineage beforeFingerprint afterFingerprint
      lineageWitness := by
  intro accepted
  exact accepted
    (ay_pcsc_FingerprintLineage beforeFingerprint afterFingerprint
      lineageWitness)
    (fun _sub rest1 =>
      rest1
        (ay_pcsc_FingerprintLineage beforeFingerprint afterFingerprint
          lineageWitness)
        (fun _res rest2 =>
          rest2
            (ay_pcsc_FingerprintLineage beforeFingerprint afterFingerprint
              lineageWitness)
            (fun _eq rest3 =>
              rest3
                (ay_pcsc_FingerprintLineage beforeFingerprint afterFingerprint
                  lineageWitness)
                (fun _model rest4 =>
                  rest4
                    (ay_pcsc_FingerprintLineage
                      beforeFingerprint afterFingerprint lineageWitness)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pcsc_FingerprintLineage
                          beforeFingerprint afterFingerprint lineageWitness)
                        (fun fp _tail => fp))))))

theorem ay_pcsc_certificate_digest
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_pcsc_ClauseSubsumptionCertificate
      beforeCnf afterCnf removedClause keptClause clauseId
      subsumptionWitness sourceClause strengthenedClause pivotLiteral
      resolutionWitness afterModel beforeModel certificate conflict
      beforeFingerprint afterFingerprint lineageWitness stepDigest
      manifestDigest certificateBundle checkerAccepted ->
    ay_pcsc_DigestMembership stepDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_pcsc_DigestMembership stepDigest manifestDigest)
    (fun _sub rest1 =>
      rest1
        (ay_pcsc_DigestMembership stepDigest manifestDigest)
        (fun _res rest2 =>
          rest2
            (ay_pcsc_DigestMembership stepDigest manifestDigest)
            (fun _eq rest3 =>
              rest3
                (ay_pcsc_DigestMembership stepDigest manifestDigest)
                (fun _model rest4 =>
                  rest4
                    (ay_pcsc_DigestMembership stepDigest manifestDigest)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pcsc_DigestMembership stepDigest manifestDigest)
                        (fun _fp rest6 =>
                          rest6
                            (ay_pcsc_DigestMembership stepDigest manifestDigest)
                            (fun digest _tail => digest)))))))

theorem ay_pcsc_certificate_checker_replay
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_pcsc_ClauseSubsumptionCertificate
      beforeCnf afterCnf removedClause keptClause clauseId
      subsumptionWitness sourceClause strengthenedClause pivotLiteral
      resolutionWitness afterModel beforeModel certificate conflict
      beforeFingerprint afterFingerprint lineageWitness stepDigest
      manifestDigest certificateBundle checkerAccepted ->
    ay_pcsc_CheckerReplay certificateBundle checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pcsc_CheckerReplay certificateBundle checkerAccepted)
    (fun _sub rest1 =>
      rest1
        (ay_pcsc_CheckerReplay certificateBundle checkerAccepted)
        (fun _res rest2 =>
          rest2
            (ay_pcsc_CheckerReplay certificateBundle checkerAccepted)
            (fun _eq rest3 =>
              rest3
                (ay_pcsc_CheckerReplay certificateBundle checkerAccepted)
                (fun _model rest4 =>
                  rest4
                    (ay_pcsc_CheckerReplay certificateBundle checkerAccepted)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pcsc_CheckerReplay certificateBundle checkerAccepted)
                        (fun _fp rest6 =>
                          rest6
                            (ay_pcsc_CheckerReplay certificateBundle checkerAccepted)
                            (fun _digest replay => replay)))))))

theorem ay_pcsc_sat_pullback
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_pcsc_ClauseSubsumptionCertificate
      beforeCnf afterCnf removedClause keptClause clauseId
      subsumptionWitness sourceClause strengthenedClause pivotLiteral
      resolutionWitness afterModel beforeModel certificate conflict
      beforeFingerprint afterFingerprint lineageWitness stepDigest
      manifestDigest certificateBundle checkerAccepted ->
    ay_pcsc_Sat afterCnf afterModel ->
    ay_pcsc_Sat beforeCnf beforeModel := by
  intro accepted afterSat
  exact
    (ay_pcsc_certificate_model_reconstruction
      beforeCnf afterCnf removedClause keptClause clauseId subsumptionWitness
      sourceClause strengthenedClause pivotLiteral resolutionWitness afterModel
      beforeModel certificate conflict beforeFingerprint afterFingerprint
      lineageWitness stepDigest manifestDigest certificateBundle
      checkerAccepted accepted)
      afterSat

theorem ay_pcsc_unsat_pushback
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_pcsc_ClauseSubsumptionCertificate
      beforeCnf afterCnf removedClause keptClause clauseId
      subsumptionWitness sourceClause strengthenedClause pivotLiteral
      resolutionWitness afterModel beforeModel certificate conflict
      beforeFingerprint afterFingerprint lineageWitness stepDigest
      manifestDigest certificateBundle checkerAccepted ->
    ay_pcsc_Replay afterCnf certificate conflict ->
    certificate ->
    beforeCnf ->
    conflict := by
  intro accepted replay cert before
  exact
    (ay_pcsc_certificate_proof_reconstruction
      beforeCnf afterCnf removedClause keptClause clauseId subsumptionWitness
      sourceClause strengthenedClause pivotLiteral resolutionWitness afterModel
      beforeModel certificate conflict beforeFingerprint afterFingerprint
      lineageWitness stepDigest manifestDigest certificateBundle
      checkerAccepted accepted)
      replay cert before

theorem ay_pcsc_public_sat
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop)
    (exitCode : Prop) :
    ay_pcsc_ClauseSubsumptionCertificate
      beforeCnf afterCnf removedClause keptClause clauseId
      subsumptionWitness sourceClause strengthenedClause pivotLiteral
      resolutionWitness afterModel beforeModel certificate conflict
      beforeFingerprint afterFingerprint lineageWitness stepDigest
      manifestDigest certificateBundle checkerAccepted ->
    ay_pcsc_Sat afterCnf afterModel ->
    exitCode ->
    ay_pcsc_PublicResult beforeCnf beforeModel certificate conflict exitCode := by
  intro accepted afterSat exit
  exact ay_pcsc_disj_left
    (ay_pcsc_ExitCodeSound exitCode (ay_pcsc_Sat beforeCnf beforeModel))
    (ay_pcsc_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))
    (ay_pcsc_conj_intro exitCode
      (ay_pcsc_Sat beforeCnf beforeModel)
      exit
      (ay_pcsc_sat_pullback
        beforeCnf afterCnf removedClause keptClause clauseId
        subsumptionWitness sourceClause strengthenedClause pivotLiteral
        resolutionWitness afterModel beforeModel certificate conflict
        beforeFingerprint afterFingerprint lineageWitness stepDigest
        manifestDigest certificateBundle checkerAccepted accepted afterSat))

theorem ay_pcsc_public_unsat
    (beforeCnf : Prop) (afterCnf : Prop)
    (removedClause : Prop) (keptClause : Prop) (clauseId : Prop)
    (subsumptionWitness : Prop)
    (sourceClause : Prop) (strengthenedClause : Prop) (pivotLiteral : Prop)
    (resolutionWitness : Prop)
    (afterModel : Prop) (beforeModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (beforeFingerprint : Prop) (afterFingerprint : Prop)
    (lineageWitness : Prop)
    (stepDigest : Prop) (manifestDigest : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop)
    (exitCode : Prop) :
    ay_pcsc_ClauseSubsumptionCertificate
      beforeCnf afterCnf removedClause keptClause clauseId
      subsumptionWitness sourceClause strengthenedClause pivotLiteral
      resolutionWitness afterModel beforeModel certificate conflict
      beforeFingerprint afterFingerprint lineageWitness stepDigest
      manifestDigest certificateBundle checkerAccepted ->
    ay_pcsc_Replay afterCnf certificate conflict ->
    exitCode ->
    ay_pcsc_PublicResult beforeCnf beforeModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_pcsc_disj_right
    (ay_pcsc_ExitCodeSound exitCode (ay_pcsc_Sat beforeCnf beforeModel))
    (ay_pcsc_ExitCodeSound exitCode (certificate -> beforeCnf -> conflict))
    (ay_pcsc_conj_intro exitCode
      (certificate -> beforeCnf -> conflict)
      exit
      (fun cert before =>
        ay_pcsc_unsat_pushback
          beforeCnf afterCnf removedClause keptClause clauseId
          subsumptionWitness sourceClause strengthenedClause pivotLiteral
          resolutionWitness afterModel beforeModel certificate conflict
          beforeFingerprint afterFingerprint lineageWitness stepDigest
          manifestDigest certificateBundle checkerAccepted accepted replay cert
          before))

theorem ay_pcsc_failure_missing_witness
    (missingWitness : Prop) (staleClauseId : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    missingWitness ->
    ay_pcsc_CertificateFailure
      missingWitness staleClauseId fingerprintMismatch digestMismatch
      replayRejected := by
  intro missing
  exact ay_pcsc_disj_left missingWitness
    (ay_pcsc_Disj staleClauseId
      (ay_pcsc_Disj fingerprintMismatch
        (ay_pcsc_Disj digestMismatch replayRejected)))
    missing

theorem ay_pcsc_failure_stale_clause_id
    (missingWitness : Prop) (staleClauseId : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    staleClauseId ->
    ay_pcsc_CertificateFailure
      missingWitness staleClauseId fingerprintMismatch digestMismatch
      replayRejected := by
  intro stale
  exact ay_pcsc_disj_right missingWitness
    (ay_pcsc_Disj staleClauseId
      (ay_pcsc_Disj fingerprintMismatch
        (ay_pcsc_Disj digestMismatch replayRejected)))
    (ay_pcsc_disj_left staleClauseId
      (ay_pcsc_Disj fingerprintMismatch
        (ay_pcsc_Disj digestMismatch replayRejected))
      stale)

theorem ay_pcsc_failure_fingerprint_mismatch
    (missingWitness : Prop) (staleClauseId : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    fingerprintMismatch ->
    ay_pcsc_CertificateFailure
      missingWitness staleClauseId fingerprintMismatch digestMismatch
      replayRejected := by
  intro mismatch
  exact ay_pcsc_disj_right missingWitness
    (ay_pcsc_Disj staleClauseId
      (ay_pcsc_Disj fingerprintMismatch
        (ay_pcsc_Disj digestMismatch replayRejected)))
    (ay_pcsc_disj_right staleClauseId
      (ay_pcsc_Disj fingerprintMismatch
        (ay_pcsc_Disj digestMismatch replayRejected))
      (ay_pcsc_disj_left fingerprintMismatch
        (ay_pcsc_Disj digestMismatch replayRejected)
        mismatch))

theorem ay_pcsc_failure_digest_mismatch
    (missingWitness : Prop) (staleClauseId : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    digestMismatch ->
    ay_pcsc_CertificateFailure
      missingWitness staleClauseId fingerprintMismatch digestMismatch
      replayRejected := by
  intro mismatch
  exact ay_pcsc_disj_right missingWitness
    (ay_pcsc_Disj staleClauseId
      (ay_pcsc_Disj fingerprintMismatch
        (ay_pcsc_Disj digestMismatch replayRejected)))
    (ay_pcsc_disj_right staleClauseId
      (ay_pcsc_Disj fingerprintMismatch
        (ay_pcsc_Disj digestMismatch replayRejected))
      (ay_pcsc_disj_right fingerprintMismatch
        (ay_pcsc_Disj digestMismatch replayRejected)
        (ay_pcsc_disj_left digestMismatch replayRejected mismatch)))

theorem ay_pcsc_failure_replay_rejected
    (missingWitness : Prop) (staleClauseId : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    replayRejected ->
    ay_pcsc_CertificateFailure
      missingWitness staleClauseId fingerprintMismatch digestMismatch
      replayRejected := by
  intro rejected
  exact ay_pcsc_disj_right missingWitness
    (ay_pcsc_Disj staleClauseId
      (ay_pcsc_Disj fingerprintMismatch
        (ay_pcsc_Disj digestMismatch replayRejected)))
    (ay_pcsc_disj_right staleClauseId
      (ay_pcsc_Disj fingerprintMismatch
        (ay_pcsc_Disj digestMismatch replayRejected))
      (ay_pcsc_disj_right fingerprintMismatch
        (ay_pcsc_Disj digestMismatch replayRejected)
        (ay_pcsc_disj_right digestMismatch replayRejected rejected)))

theorem ay_pcsc_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingWitness : Prop) (staleClauseId : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcsc_DiagnosticCertificateLogEntry
      previousLog nextLog currentCnf missingWitness staleClauseId
      fingerprintMismatch digestMismatch replayRejected recompute diagnostic ->
    ay_pcsc_CertificateFailure
      missingWitness staleClauseId fingerprintMismatch digestMismatch
      replayRejected := by
  intro entry
  exact entry
    (ay_pcsc_CertificateFailure
      missingWitness staleClauseId fingerprintMismatch digestMismatch
      replayRejected)
    (fun _previous rest1 =>
      rest1
        (ay_pcsc_CertificateFailure
          missingWitness staleClauseId fingerprintMismatch digestMismatch
          replayRejected)
        (fun body _next =>
          body
            (ay_pcsc_CertificateFailure
              missingWitness staleClauseId fingerprintMismatch digestMismatch
              replayRejected)
            (fun failure _tail => failure)))

theorem ay_pcsc_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingWitness : Prop) (staleClauseId : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcsc_DiagnosticCertificateLogEntry
      previousLog nextLog currentCnf missingWitness staleClauseId
      fingerprintMismatch digestMismatch replayRejected recompute diagnostic ->
    ay_pcsc_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_pcsc_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_pcsc_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_pcsc_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_pcsc_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_pcsc_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingWitness : Prop) (staleClauseId : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcsc_DiagnosticCertificateLogEntry
      previousLog nextLog currentCnf missingWitness staleClauseId
      fingerprintMismatch digestMismatch replayRejected recompute diagnostic ->
    ay_pcsc_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_pcsc_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_pcsc_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_pcsc_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_pcsc_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_pcsc_failure_no_claim
    (missingWitness : Prop) (staleClauseId : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (diagnostic : Prop) :
    ay_pcsc_CertificateFailure
      missingWitness staleClauseId fingerprintMismatch digestMismatch
      replayRejected ->
    diagnostic ->
    ay_pcsc_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
