-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Variable-elimination replay soundness for preprocessing. The
-- propositions stand for replayable clause coverage, elimination pivot evidence, representative-map
-- agreement, model/proof reconstruction, digest membership, checker replay,
-- original fingerprint agreement, diagnostics, and public SAT/UNSAT reports.

def ay_pver_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pver_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pver_Equisat (before : Prop) (after : Prop) :=
  ay_pver_Conj (before -> after) (after -> before)

def ay_pver_Sat (cnf : Prop) (model : Prop) :=
  ay_pver_Conj cnf model

def ay_pver_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pver_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pver_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pver_ClauseCoverage
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop) :=
  ay_pver_Conj coverageWitness
    (resolvents -> coveredClauses)

def ay_pver_RepresentativeAgreement
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop) :=
  ay_pver_Conj representativeWitness
    (ay_pver_IdMatch oldRepresentative newRepresentative)

def ay_pver_ModelReconstruction
    (residualCnf : Prop) (originalCnf : Prop)
    (residualModel : Prop) (originalModel : Prop) :=
  ay_pver_Sat residualCnf residualModel ->
    ay_pver_Sat originalCnf originalModel

def ay_pver_ProofReconstruction
    (originalCnf : Prop) (residualCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pver_Replay residualCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pver_DigestMembership
    (eliminationDigest : Prop) (manifestDigest : Prop) :=
  ay_pver_Conj eliminationDigest manifestDigest

def ay_pver_CheckerReplay
    (eliminationCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pver_Conj eliminationCertificate checkerAccepted

def ay_pver_FingerprintAgreement
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pver_Conj fingerprintWitness
    (ay_pver_IdMatch originalFingerprint residualFingerprint)

def ay_pver_AcceptedVariableEliminationReplay
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pver_Conj
    (ay_pver_ClauseCoverage
      resolvents coveredClauses coverageWitness)
    (ay_pver_Conj
      (ay_pver_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_pver_Conj
        (ay_pver_Equisat originalCnf residualCnf)
        (ay_pver_Conj
          (ay_pver_ModelReconstruction
            residualCnf originalCnf residualModel originalModel)
          (ay_pver_Conj
            (ay_pver_ProofReconstruction
              originalCnf residualCnf certificate conflict)
            (ay_pver_Conj
              (ay_pver_DigestMembership eliminationDigest manifestDigest)
              (ay_pver_Conj
                (ay_pver_CheckerReplay
                  eliminationCertificate checkerAccepted)
                (ay_pver_FingerprintAgreement
                  originalFingerprint residualFingerprint
                  fingerprintWitness)))))))

def ay_pver_AcceptedVariableEliminationLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pver_Conj previousLog
    (ay_pver_Conj
      (ay_pver_AcceptedVariableEliminationReplay
        originalCnf residualCnf resolvents coveredClauses
        coverageWitness oldRepresentative newRepresentative
        representativeWitness residualModel originalModel certificate conflict
        eliminationDigest manifestDigest eliminationCertificate checkerAccepted
        originalFingerprint residualFingerprint fingerprintWitness)
      nextLog)

def ay_pver_VariableEliminationFailure
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop) :=
  ay_pver_Disj resolventMismatch
    (ay_pver_Disj missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))))

def ay_pver_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pver_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pver_Conj currentCnf recompute

def ay_pver_DiagnosticVariableEliminationLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pver_Conj previousLog
    (ay_pver_Conj
      (ay_pver_Conj
        (ay_pver_VariableEliminationFailure
          resolventMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedElimination)
        (ay_pver_Conj
          (ay_pver_RecomputeObligation currentCnf recompute)
          (ay_pver_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pver_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pver_Conj exitCode claim

def ay_pver_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pver_Disj
    (ay_pver_ExitCodeSound exitCode (ay_pver_Sat originalCnf model))
    (ay_pver_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pver_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pver_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pver_conj_left
    (left : Prop) (right : Prop) :
    ay_pver_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pver_conj_right
    (left : Prop) (right : Prop) :
    ay_pver_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pver_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pver_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pver_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pver_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pver_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pver_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pver_conj_left (before -> after) (after -> before) eq

theorem ay_pver_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pver_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pver_conj_right (before -> after) (after -> before) eq

theorem ay_pver_resolvent_coverage
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pver_AcceptedVariableEliminationReplay
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      eliminationDigest manifestDigest eliminationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pver_ClauseCoverage resolvents coveredClauses coverageWitness := by
  intro accepted
  exact ay_pver_conj_left
    (ay_pver_ClauseCoverage resolvents coveredClauses coverageWitness)
    (ay_pver_Conj
      (ay_pver_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_pver_Conj
        (ay_pver_Equisat originalCnf residualCnf)
        (ay_pver_Conj
          (ay_pver_ModelReconstruction
            residualCnf originalCnf residualModel originalModel)
          (ay_pver_Conj
            (ay_pver_ProofReconstruction
              originalCnf residualCnf certificate conflict)
            (ay_pver_Conj
              (ay_pver_DigestMembership eliminationDigest manifestDigest)
              (ay_pver_Conj
                (ay_pver_CheckerReplay eliminationCertificate checkerAccepted)
                (ay_pver_FingerprintAgreement
                  originalFingerprint residualFingerprint
                  fingerprintWitness)))))))
    accepted

theorem ay_pver_elimination_representative
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pver_AcceptedVariableEliminationReplay
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      eliminationDigest manifestDigest eliminationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pver_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness := by
  intro accepted
  exact accepted
    (ay_pver_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_pver_RepresentativeAgreement
          oldRepresentative newRepresentative representativeWitness)
        (fun rep _tail => rep))

theorem ay_pver_elimination_equisat
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pver_AcceptedVariableEliminationReplay
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      eliminationDigest manifestDigest eliminationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pver_Equisat originalCnf residualCnf := by
  intro accepted
  exact accepted
    (ay_pver_Equisat originalCnf residualCnf)
    (fun _coverage rest1 =>
      rest1
        (ay_pver_Equisat originalCnf residualCnf)
        (fun _rep rest2 =>
          rest2
            (ay_pver_Equisat originalCnf residualCnf)
            (fun eq _tail => eq)))

theorem ay_pver_elimination_model_reconstruction
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pver_AcceptedVariableEliminationReplay
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      eliminationDigest manifestDigest eliminationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pver_ModelReconstruction residualCnf originalCnf residualModel
      originalModel := by
  intro accepted
  exact accepted
    (ay_pver_ModelReconstruction
      residualCnf originalCnf residualModel originalModel)
    (fun _coverage rest1 =>
      rest1
        (ay_pver_ModelReconstruction
          residualCnf originalCnf residualModel originalModel)
        (fun _rep rest2 =>
          rest2
            (ay_pver_ModelReconstruction
              residualCnf originalCnf residualModel originalModel)
            (fun _eq rest3 =>
              rest3
                (ay_pver_ModelReconstruction
                  residualCnf originalCnf residualModel originalModel)
                (fun model _tail => model))))

theorem ay_pver_elimination_proof_reconstruction
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pver_AcceptedVariableEliminationReplay
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      eliminationDigest manifestDigest eliminationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pver_ProofReconstruction originalCnf residualCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_pver_ProofReconstruction originalCnf residualCnf certificate conflict)
    (fun _coverage rest1 =>
      rest1
        (ay_pver_ProofReconstruction originalCnf residualCnf certificate conflict)
        (fun _rep rest2 =>
          rest2
            (ay_pver_ProofReconstruction
              originalCnf residualCnf certificate conflict)
            (fun _eq rest3 =>
              rest3
                (ay_pver_ProofReconstruction
                  originalCnf residualCnf certificate conflict)
                (fun _model rest4 =>
                  rest4
                    (ay_pver_ProofReconstruction
                      originalCnf residualCnf certificate conflict)
                    (fun proof _tail => proof)))))

theorem ay_pver_elimination_digest
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pver_AcceptedVariableEliminationReplay
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      eliminationDigest manifestDigest eliminationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pver_DigestMembership eliminationDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_pver_DigestMembership eliminationDigest manifestDigest)
    (fun _coverage rest1 =>
      rest1
        (ay_pver_DigestMembership eliminationDigest manifestDigest)
        (fun _rep rest2 =>
          rest2
            (ay_pver_DigestMembership eliminationDigest manifestDigest)
            (fun _eq rest3 =>
              rest3
                (ay_pver_DigestMembership eliminationDigest manifestDigest)
                (fun _model rest4 =>
                  rest4
                    (ay_pver_DigestMembership eliminationDigest manifestDigest)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pver_DigestMembership eliminationDigest manifestDigest)
                        (fun digest _tail => digest))))))

theorem ay_pver_elimination_checker
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pver_AcceptedVariableEliminationReplay
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      eliminationDigest manifestDigest eliminationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pver_CheckerReplay eliminationCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pver_CheckerReplay eliminationCertificate checkerAccepted)
    (fun _coverage rest1 =>
      rest1
        (ay_pver_CheckerReplay eliminationCertificate checkerAccepted)
        (fun _rep rest2 =>
          rest2
            (ay_pver_CheckerReplay eliminationCertificate checkerAccepted)
            (fun _eq rest3 =>
              rest3
                (ay_pver_CheckerReplay eliminationCertificate checkerAccepted)
                (fun _model rest4 =>
                  rest4
                    (ay_pver_CheckerReplay eliminationCertificate checkerAccepted)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pver_CheckerReplay
                          eliminationCertificate checkerAccepted)
                        (fun _digest rest6 =>
                          rest6
                            (ay_pver_CheckerReplay
                              eliminationCertificate checkerAccepted)
                            (fun checker _tail => checker)))))))

theorem ay_pver_elimination_fingerprint
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pver_AcceptedVariableEliminationReplay
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      eliminationDigest manifestDigest eliminationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pver_FingerprintAgreement
      originalFingerprint residualFingerprint fingerprintWitness := by
  intro accepted
  exact accepted
    (ay_pver_FingerprintAgreement
      originalFingerprint residualFingerprint fingerprintWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_pver_FingerprintAgreement
          originalFingerprint residualFingerprint fingerprintWitness)
        (fun _rep rest2 =>
          rest2
            (ay_pver_FingerprintAgreement
              originalFingerprint residualFingerprint fingerprintWitness)
            (fun _eq rest3 =>
              rest3
                (ay_pver_FingerprintAgreement
                  originalFingerprint residualFingerprint fingerprintWitness)
                (fun _model rest4 =>
                  rest4
                    (ay_pver_FingerprintAgreement
                      originalFingerprint residualFingerprint fingerprintWitness)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pver_FingerprintAgreement
                          originalFingerprint residualFingerprint
                          fingerprintWitness)
                        (fun _digest rest6 =>
                          rest6
                            (ay_pver_FingerprintAgreement
                              originalFingerprint residualFingerprint
                              fingerprintWitness)
                            (fun _checker fp => fp)))))))

theorem ay_pver_sat_pullback
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pver_AcceptedVariableEliminationReplay
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      eliminationDigest manifestDigest eliminationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pver_Sat residualCnf residualModel ->
    ay_pver_Sat originalCnf originalModel := by
  intro accepted residualSat
  exact
    (ay_pver_elimination_model_reconstruction
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative representativeWitness
      residualModel originalModel certificate conflict eliminationDigest
      manifestDigest eliminationCertificate checkerAccepted originalFingerprint
      residualFingerprint fingerprintWitness accepted)
      residualSat

theorem ay_pver_unsat_pushback
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pver_AcceptedVariableEliminationReplay
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      eliminationDigest manifestDigest eliminationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pver_Replay residualCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay cert original
  exact
    (ay_pver_elimination_proof_reconstruction
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative representativeWitness
      residualModel originalModel certificate conflict eliminationDigest
      manifestDigest eliminationCertificate checkerAccepted originalFingerprint
      residualFingerprint fingerprintWitness accepted)
      replay cert original

theorem ay_pver_public_sat
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pver_AcceptedVariableEliminationReplay
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      eliminationDigest manifestDigest eliminationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pver_Sat residualCnf residualModel ->
    exitCode ->
    ay_pver_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted residualSat exit
  exact ay_pver_disj_left
    (ay_pver_ExitCodeSound exitCode (ay_pver_Sat originalCnf originalModel))
    (ay_pver_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pver_conj_intro exitCode
      (ay_pver_Sat originalCnf originalModel)
      exit
      (ay_pver_sat_pullback
        originalCnf residualCnf resolvents coveredClauses
        coverageWitness oldRepresentative newRepresentative representativeWitness
        residualModel originalModel certificate conflict eliminationDigest
        manifestDigest eliminationCertificate checkerAccepted originalFingerprint
        residualFingerprint fingerprintWitness accepted residualSat))

theorem ay_pver_public_unsat
    (originalCnf : Prop) (residualCnf : Prop)
    (resolvents : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (eliminationDigest : Prop) (manifestDigest : Prop)
    (eliminationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pver_AcceptedVariableEliminationReplay
      originalCnf residualCnf resolvents coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      eliminationDigest manifestDigest eliminationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pver_Replay residualCnf certificate conflict ->
    exitCode ->
    ay_pver_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_pver_disj_right
    (ay_pver_ExitCodeSound exitCode (ay_pver_Sat originalCnf originalModel))
    (ay_pver_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pver_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      exit
      (fun cert original =>
        ay_pver_unsat_pushback
          originalCnf residualCnf resolvents coveredClauses
          coverageWitness oldRepresentative newRepresentative
          representativeWitness residualModel originalModel certificate conflict
          eliminationDigest manifestDigest eliminationCertificate checkerAccepted
          originalFingerprint residualFingerprint fingerprintWitness accepted
          replay cert original))

theorem ay_pver_failure_resolvent_mismatch
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop) :
    resolventMismatch ->
    ay_pver_VariableEliminationFailure
      resolventMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedElimination := by
  intro mismatch
  exact ay_pver_disj_left resolventMismatch
    (ay_pver_Disj missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))))
    mismatch

theorem ay_pver_failure_missing_coverage
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop) :
    missingCoverage ->
    ay_pver_VariableEliminationFailure
      resolventMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedElimination := by
  intro missing
  exact ay_pver_disj_right resolventMismatch
    (ay_pver_Disj missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))))
    (ay_pver_disj_left missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)))))
      missing)

theorem ay_pver_failure_representative_mismatch
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop) :
    representativeMismatch ->
    ay_pver_VariableEliminationFailure
      resolventMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedElimination := by
  intro mismatch
  exact ay_pver_disj_right resolventMismatch
    (ay_pver_Disj missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))))
    (ay_pver_disj_right missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)))))
      (ay_pver_disj_left representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))
        mismatch))

theorem ay_pver_failure_broken_reconstruction
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop) :
    brokenReconstruction ->
    ay_pver_VariableEliminationFailure
      resolventMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedElimination := by
  intro broken
  exact ay_pver_disj_right resolventMismatch
    (ay_pver_Disj missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))))
    (ay_pver_disj_right missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)))))
      (ay_pver_disj_right representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))
        (ay_pver_disj_left brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)))
          broken)))

theorem ay_pver_failure_digest_mismatch
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop) :
    digestMismatch ->
    ay_pver_VariableEliminationFailure
      resolventMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedElimination := by
  intro mismatch
  exact ay_pver_disj_right resolventMismatch
    (ay_pver_Disj missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))))
    (ay_pver_disj_right missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)))))
      (ay_pver_disj_right representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))
        (ay_pver_disj_right brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)))
          (ay_pver_disj_left digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))
            mismatch))))

theorem ay_pver_failure_replay_rejected
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop) :
    replayRejected ->
    ay_pver_VariableEliminationFailure
      resolventMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedElimination := by
  intro rejected
  exact ay_pver_disj_right resolventMismatch
    (ay_pver_Disj missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))))
    (ay_pver_disj_right missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)))))
      (ay_pver_disj_right representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))
        (ay_pver_disj_right brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)))
          (ay_pver_disj_right digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))
            (ay_pver_disj_left replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)
              rejected)))))

theorem ay_pver_failure_fingerprint_drift
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop) :
    fingerprintDrift ->
    ay_pver_VariableEliminationFailure
      resolventMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedElimination := by
  intro drift
  exact ay_pver_disj_right resolventMismatch
    (ay_pver_Disj missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))))
    (ay_pver_disj_right missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)))))
      (ay_pver_disj_right representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))
        (ay_pver_disj_right brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)))
          (ay_pver_disj_right digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))
            (ay_pver_disj_right replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)
              (ay_pver_disj_left fingerprintDrift uncheckedElimination drift))))))

theorem ay_pver_failure_unchecked_elimination
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop) :
    uncheckedElimination ->
    ay_pver_VariableEliminationFailure
      resolventMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedElimination := by
  intro unchecked
  exact ay_pver_disj_right resolventMismatch
    (ay_pver_Disj missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))))
    (ay_pver_disj_right missingCoverage
      (ay_pver_Disj representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)))))
      (ay_pver_disj_right representativeMismatch
        (ay_pver_Disj brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))))
        (ay_pver_disj_right brokenReconstruction
          (ay_pver_Disj digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)))
          (ay_pver_disj_right digestMismatch
            (ay_pver_Disj replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination))
            (ay_pver_disj_right replayRejected
              (ay_pver_Disj fingerprintDrift uncheckedElimination)
              (ay_pver_disj_right fingerprintDrift uncheckedElimination
                unchecked))))))

theorem ay_pver_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pver_DiagnosticVariableEliminationLogEntry
      previousLog nextLog currentCnf resolventMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedElimination recompute diagnostic ->
    ay_pver_VariableEliminationFailure
      resolventMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedElimination := by
  intro entry
  exact entry
    (ay_pver_VariableEliminationFailure
      resolventMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedElimination)
    (fun _previous rest1 =>
      rest1
        (ay_pver_VariableEliminationFailure
          resolventMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedElimination)
        (fun body _next =>
          body
            (ay_pver_VariableEliminationFailure
              resolventMismatch missingCoverage representativeMismatch
              brokenReconstruction digestMismatch replayRejected fingerprintDrift
              uncheckedElimination)
            (fun failure _tail => failure)))

theorem ay_pver_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pver_DiagnosticVariableEliminationLogEntry
      previousLog nextLog currentCnf resolventMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedElimination recompute diagnostic ->
    ay_pver_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_pver_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_pver_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_pver_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_pver_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_pver_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pver_DiagnosticVariableEliminationLogEntry
      previousLog nextLog currentCnf resolventMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedElimination recompute diagnostic ->
    ay_pver_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_pver_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_pver_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_pver_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_pver_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_pver_unchecked_elimination_no_public_blessing
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop)
    (diagnostic : Prop) :
    uncheckedElimination ->
    diagnostic ->
    ay_pver_NoSemanticClaim diagnostic := by
  intro _unchecked diag
  exact diag

theorem ay_pver_failure_no_claim
    (resolventMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedElimination : Prop)
    (diagnostic : Prop) :
    ay_pver_VariableEliminationFailure
      resolventMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedElimination ->
    diagnostic ->
    ay_pver_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
