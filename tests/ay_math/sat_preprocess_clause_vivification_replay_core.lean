-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Clause vivification replay soundness for preprocessing. The
-- propositions stand for replayable clause coverage, representative-map
-- agreement, model/proof reconstruction, digest membership, checker replay,
-- original fingerprint agreement, diagnostics, and public SAT/UNSAT reports.

def ay_pcvr_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pcvr_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pcvr_Equisat (before : Prop) (after : Prop) :=
  ay_pcvr_Conj (before -> after) (after -> before)

def ay_pcvr_Sat (cnf : Prop) (model : Prop) :=
  ay_pcvr_Conj cnf model

def ay_pcvr_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pcvr_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pcvr_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pcvr_ClauseCoverage
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop) :=
  ay_pcvr_Conj coverageWitness
    (vivifiedClauses -> coveredClauses)

def ay_pcvr_RepresentativeAgreement
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop) :=
  ay_pcvr_Conj representativeWitness
    (ay_pcvr_IdMatch oldRepresentative newRepresentative)

def ay_pcvr_ModelReconstruction
    (residualCnf : Prop) (originalCnf : Prop)
    (residualModel : Prop) (originalModel : Prop) :=
  ay_pcvr_Sat residualCnf residualModel ->
    ay_pcvr_Sat originalCnf originalModel

def ay_pcvr_ProofReconstruction
    (originalCnf : Prop) (residualCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pcvr_Replay residualCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pcvr_DigestMembership
    (vivificationDigest : Prop) (manifestDigest : Prop) :=
  ay_pcvr_Conj vivificationDigest manifestDigest

def ay_pcvr_CheckerReplay
    (vivificationCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pcvr_Conj vivificationCertificate checkerAccepted

def ay_pcvr_FingerprintAgreement
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pcvr_Conj fingerprintWitness
    (ay_pcvr_IdMatch originalFingerprint residualFingerprint)

def ay_pcvr_AcceptedVivificationReplay
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pcvr_Conj
    (ay_pcvr_ClauseCoverage
      vivifiedClauses coveredClauses coverageWitness)
    (ay_pcvr_Conj
      (ay_pcvr_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_pcvr_Conj
        (ay_pcvr_Equisat originalCnf residualCnf)
        (ay_pcvr_Conj
          (ay_pcvr_ModelReconstruction
            residualCnf originalCnf residualModel originalModel)
          (ay_pcvr_Conj
            (ay_pcvr_ProofReconstruction
              originalCnf residualCnf certificate conflict)
            (ay_pcvr_Conj
              (ay_pcvr_DigestMembership vivificationDigest manifestDigest)
              (ay_pcvr_Conj
                (ay_pcvr_CheckerReplay
                  vivificationCertificate checkerAccepted)
                (ay_pcvr_FingerprintAgreement
                  originalFingerprint residualFingerprint
                  fingerprintWitness)))))))

def ay_pcvr_AcceptedVivificationLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pcvr_Conj previousLog
    (ay_pcvr_Conj
      (ay_pcvr_AcceptedVivificationReplay
        originalCnf residualCnf vivifiedClauses coveredClauses
        coverageWitness oldRepresentative newRepresentative
        representativeWitness residualModel originalModel certificate conflict
        vivificationDigest manifestDigest vivificationCertificate checkerAccepted
        originalFingerprint residualFingerprint fingerprintWitness)
      nextLog)

def ay_pcvr_VivificationFailure
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop) :=
  ay_pcvr_Disj literalDeletionMismatch
    (ay_pcvr_Disj missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))))

def ay_pcvr_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pcvr_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pcvr_Conj currentCnf recompute

def ay_pcvr_DiagnosticVivificationLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pcvr_Conj previousLog
    (ay_pcvr_Conj
      (ay_pcvr_Conj
        (ay_pcvr_VivificationFailure
          literalDeletionMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedVivification)
        (ay_pcvr_Conj
          (ay_pcvr_RecomputeObligation currentCnf recompute)
          (ay_pcvr_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pcvr_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pcvr_Conj exitCode claim

def ay_pcvr_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pcvr_Disj
    (ay_pcvr_ExitCodeSound exitCode (ay_pcvr_Sat originalCnf model))
    (ay_pcvr_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pcvr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pcvr_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pcvr_conj_left
    (left : Prop) (right : Prop) :
    ay_pcvr_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pcvr_conj_right
    (left : Prop) (right : Prop) :
    ay_pcvr_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pcvr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pcvr_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pcvr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pcvr_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pcvr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pcvr_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pcvr_conj_left (before -> after) (after -> before) eq

theorem ay_pcvr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pcvr_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pcvr_conj_right (before -> after) (after -> before) eq

theorem ay_pcvr_vivification_clause_coverage
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pcvr_AcceptedVivificationReplay
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      vivificationDigest manifestDigest vivificationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pcvr_ClauseCoverage vivifiedClauses coveredClauses coverageWitness := by
  intro accepted
  exact ay_pcvr_conj_left
    (ay_pcvr_ClauseCoverage vivifiedClauses coveredClauses coverageWitness)
    (ay_pcvr_Conj
      (ay_pcvr_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_pcvr_Conj
        (ay_pcvr_Equisat originalCnf residualCnf)
        (ay_pcvr_Conj
          (ay_pcvr_ModelReconstruction
            residualCnf originalCnf residualModel originalModel)
          (ay_pcvr_Conj
            (ay_pcvr_ProofReconstruction
              originalCnf residualCnf certificate conflict)
            (ay_pcvr_Conj
              (ay_pcvr_DigestMembership vivificationDigest manifestDigest)
              (ay_pcvr_Conj
                (ay_pcvr_CheckerReplay vivificationCertificate checkerAccepted)
                (ay_pcvr_FingerprintAgreement
                  originalFingerprint residualFingerprint
                  fingerprintWitness)))))))
    accepted

theorem ay_pcvr_vivification_representative
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pcvr_AcceptedVivificationReplay
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      vivificationDigest manifestDigest vivificationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pcvr_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness := by
  intro accepted
  exact accepted
    (ay_pcvr_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_pcvr_RepresentativeAgreement
          oldRepresentative newRepresentative representativeWitness)
        (fun rep _tail => rep))

theorem ay_pcvr_vivification_equisat
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pcvr_AcceptedVivificationReplay
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      vivificationDigest manifestDigest vivificationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pcvr_Equisat originalCnf residualCnf := by
  intro accepted
  exact accepted
    (ay_pcvr_Equisat originalCnf residualCnf)
    (fun _coverage rest1 =>
      rest1
        (ay_pcvr_Equisat originalCnf residualCnf)
        (fun _rep rest2 =>
          rest2
            (ay_pcvr_Equisat originalCnf residualCnf)
            (fun eq _tail => eq)))

theorem ay_pcvr_vivification_model_reconstruction
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pcvr_AcceptedVivificationReplay
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      vivificationDigest manifestDigest vivificationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pcvr_ModelReconstruction residualCnf originalCnf residualModel
      originalModel := by
  intro accepted
  exact accepted
    (ay_pcvr_ModelReconstruction
      residualCnf originalCnf residualModel originalModel)
    (fun _coverage rest1 =>
      rest1
        (ay_pcvr_ModelReconstruction
          residualCnf originalCnf residualModel originalModel)
        (fun _rep rest2 =>
          rest2
            (ay_pcvr_ModelReconstruction
              residualCnf originalCnf residualModel originalModel)
            (fun _eq rest3 =>
              rest3
                (ay_pcvr_ModelReconstruction
                  residualCnf originalCnf residualModel originalModel)
                (fun model _tail => model))))

theorem ay_pcvr_vivification_proof_reconstruction
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pcvr_AcceptedVivificationReplay
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      vivificationDigest manifestDigest vivificationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pcvr_ProofReconstruction originalCnf residualCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_pcvr_ProofReconstruction originalCnf residualCnf certificate conflict)
    (fun _coverage rest1 =>
      rest1
        (ay_pcvr_ProofReconstruction originalCnf residualCnf certificate conflict)
        (fun _rep rest2 =>
          rest2
            (ay_pcvr_ProofReconstruction
              originalCnf residualCnf certificate conflict)
            (fun _eq rest3 =>
              rest3
                (ay_pcvr_ProofReconstruction
                  originalCnf residualCnf certificate conflict)
                (fun _model rest4 =>
                  rest4
                    (ay_pcvr_ProofReconstruction
                      originalCnf residualCnf certificate conflict)
                    (fun proof _tail => proof)))))

theorem ay_pcvr_vivification_digest
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pcvr_AcceptedVivificationReplay
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      vivificationDigest manifestDigest vivificationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pcvr_DigestMembership vivificationDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_pcvr_DigestMembership vivificationDigest manifestDigest)
    (fun _coverage rest1 =>
      rest1
        (ay_pcvr_DigestMembership vivificationDigest manifestDigest)
        (fun _rep rest2 =>
          rest2
            (ay_pcvr_DigestMembership vivificationDigest manifestDigest)
            (fun _eq rest3 =>
              rest3
                (ay_pcvr_DigestMembership vivificationDigest manifestDigest)
                (fun _model rest4 =>
                  rest4
                    (ay_pcvr_DigestMembership vivificationDigest manifestDigest)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pcvr_DigestMembership vivificationDigest manifestDigest)
                        (fun digest _tail => digest))))))

theorem ay_pcvr_vivification_checker
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pcvr_AcceptedVivificationReplay
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      vivificationDigest manifestDigest vivificationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pcvr_CheckerReplay vivificationCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pcvr_CheckerReplay vivificationCertificate checkerAccepted)
    (fun _coverage rest1 =>
      rest1
        (ay_pcvr_CheckerReplay vivificationCertificate checkerAccepted)
        (fun _rep rest2 =>
          rest2
            (ay_pcvr_CheckerReplay vivificationCertificate checkerAccepted)
            (fun _eq rest3 =>
              rest3
                (ay_pcvr_CheckerReplay vivificationCertificate checkerAccepted)
                (fun _model rest4 =>
                  rest4
                    (ay_pcvr_CheckerReplay vivificationCertificate checkerAccepted)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pcvr_CheckerReplay
                          vivificationCertificate checkerAccepted)
                        (fun _digest rest6 =>
                          rest6
                            (ay_pcvr_CheckerReplay
                              vivificationCertificate checkerAccepted)
                            (fun checker _tail => checker)))))))

theorem ay_pcvr_vivification_fingerprint
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pcvr_AcceptedVivificationReplay
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      vivificationDigest manifestDigest vivificationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pcvr_FingerprintAgreement
      originalFingerprint residualFingerprint fingerprintWitness := by
  intro accepted
  exact accepted
    (ay_pcvr_FingerprintAgreement
      originalFingerprint residualFingerprint fingerprintWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_pcvr_FingerprintAgreement
          originalFingerprint residualFingerprint fingerprintWitness)
        (fun _rep rest2 =>
          rest2
            (ay_pcvr_FingerprintAgreement
              originalFingerprint residualFingerprint fingerprintWitness)
            (fun _eq rest3 =>
              rest3
                (ay_pcvr_FingerprintAgreement
                  originalFingerprint residualFingerprint fingerprintWitness)
                (fun _model rest4 =>
                  rest4
                    (ay_pcvr_FingerprintAgreement
                      originalFingerprint residualFingerprint fingerprintWitness)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pcvr_FingerprintAgreement
                          originalFingerprint residualFingerprint
                          fingerprintWitness)
                        (fun _digest rest6 =>
                          rest6
                            (ay_pcvr_FingerprintAgreement
                              originalFingerprint residualFingerprint
                              fingerprintWitness)
                            (fun _checker fp => fp)))))))

theorem ay_pcvr_sat_pullback
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pcvr_AcceptedVivificationReplay
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      vivificationDigest manifestDigest vivificationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pcvr_Sat residualCnf residualModel ->
    ay_pcvr_Sat originalCnf originalModel := by
  intro accepted residualSat
  exact
    (ay_pcvr_vivification_model_reconstruction
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative representativeWitness
      residualModel originalModel certificate conflict vivificationDigest
      manifestDigest vivificationCertificate checkerAccepted originalFingerprint
      residualFingerprint fingerprintWitness accepted)
      residualSat

theorem ay_pcvr_unsat_pushback
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pcvr_AcceptedVivificationReplay
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      vivificationDigest manifestDigest vivificationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pcvr_Replay residualCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay cert original
  exact
    (ay_pcvr_vivification_proof_reconstruction
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative representativeWitness
      residualModel originalModel certificate conflict vivificationDigest
      manifestDigest vivificationCertificate checkerAccepted originalFingerprint
      residualFingerprint fingerprintWitness accepted)
      replay cert original

theorem ay_pcvr_public_sat
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pcvr_AcceptedVivificationReplay
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      vivificationDigest manifestDigest vivificationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pcvr_Sat residualCnf residualModel ->
    exitCode ->
    ay_pcvr_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted residualSat exit
  exact ay_pcvr_disj_left
    (ay_pcvr_ExitCodeSound exitCode (ay_pcvr_Sat originalCnf originalModel))
    (ay_pcvr_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pcvr_conj_intro exitCode
      (ay_pcvr_Sat originalCnf originalModel)
      exit
      (ay_pcvr_sat_pullback
        originalCnf residualCnf vivifiedClauses coveredClauses
        coverageWitness oldRepresentative newRepresentative representativeWitness
        residualModel originalModel certificate conflict vivificationDigest
        manifestDigest vivificationCertificate checkerAccepted originalFingerprint
        residualFingerprint fingerprintWitness accepted residualSat))

theorem ay_pcvr_public_unsat
    (originalCnf : Prop) (residualCnf : Prop)
    (vivifiedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (vivificationDigest : Prop) (manifestDigest : Prop)
    (vivificationCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pcvr_AcceptedVivificationReplay
      originalCnf residualCnf vivifiedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      vivificationDigest manifestDigest vivificationCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_pcvr_Replay residualCnf certificate conflict ->
    exitCode ->
    ay_pcvr_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_pcvr_disj_right
    (ay_pcvr_ExitCodeSound exitCode (ay_pcvr_Sat originalCnf originalModel))
    (ay_pcvr_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pcvr_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      exit
      (fun cert original =>
        ay_pcvr_unsat_pushback
          originalCnf residualCnf vivifiedClauses coveredClauses
          coverageWitness oldRepresentative newRepresentative
          representativeWitness residualModel originalModel certificate conflict
          vivificationDigest manifestDigest vivificationCertificate checkerAccepted
          originalFingerprint residualFingerprint fingerprintWitness accepted
          replay cert original))

theorem ay_pcvr_failure_literal_deletion_mismatch
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop) :
    literalDeletionMismatch ->
    ay_pcvr_VivificationFailure
      literalDeletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedVivification := by
  intro mismatch
  exact ay_pcvr_disj_left literalDeletionMismatch
    (ay_pcvr_Disj missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))))
    mismatch

theorem ay_pcvr_failure_missing_coverage
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop) :
    missingCoverage ->
    ay_pcvr_VivificationFailure
      literalDeletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedVivification := by
  intro missing
  exact ay_pcvr_disj_right literalDeletionMismatch
    (ay_pcvr_Disj missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))))
    (ay_pcvr_disj_left missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)))))
      missing)

theorem ay_pcvr_failure_representative_mismatch
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop) :
    representativeMismatch ->
    ay_pcvr_VivificationFailure
      literalDeletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedVivification := by
  intro mismatch
  exact ay_pcvr_disj_right literalDeletionMismatch
    (ay_pcvr_Disj missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))))
    (ay_pcvr_disj_right missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)))))
      (ay_pcvr_disj_left representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))
        mismatch))

theorem ay_pcvr_failure_broken_reconstruction
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop) :
    brokenReconstruction ->
    ay_pcvr_VivificationFailure
      literalDeletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedVivification := by
  intro broken
  exact ay_pcvr_disj_right literalDeletionMismatch
    (ay_pcvr_Disj missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))))
    (ay_pcvr_disj_right missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)))))
      (ay_pcvr_disj_right representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))
        (ay_pcvr_disj_left brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)))
          broken)))

theorem ay_pcvr_failure_digest_mismatch
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop) :
    digestMismatch ->
    ay_pcvr_VivificationFailure
      literalDeletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedVivification := by
  intro mismatch
  exact ay_pcvr_disj_right literalDeletionMismatch
    (ay_pcvr_Disj missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))))
    (ay_pcvr_disj_right missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)))))
      (ay_pcvr_disj_right representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))
        (ay_pcvr_disj_right brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)))
          (ay_pcvr_disj_left digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))
            mismatch))))

theorem ay_pcvr_failure_replay_rejected
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop) :
    replayRejected ->
    ay_pcvr_VivificationFailure
      literalDeletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedVivification := by
  intro rejected
  exact ay_pcvr_disj_right literalDeletionMismatch
    (ay_pcvr_Disj missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))))
    (ay_pcvr_disj_right missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)))))
      (ay_pcvr_disj_right representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))
        (ay_pcvr_disj_right brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)))
          (ay_pcvr_disj_right digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))
            (ay_pcvr_disj_left replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)
              rejected)))))

theorem ay_pcvr_failure_fingerprint_drift
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop) :
    fingerprintDrift ->
    ay_pcvr_VivificationFailure
      literalDeletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedVivification := by
  intro drift
  exact ay_pcvr_disj_right literalDeletionMismatch
    (ay_pcvr_Disj missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))))
    (ay_pcvr_disj_right missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)))))
      (ay_pcvr_disj_right representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))
        (ay_pcvr_disj_right brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)))
          (ay_pcvr_disj_right digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))
            (ay_pcvr_disj_right replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)
              (ay_pcvr_disj_left fingerprintDrift uncheckedVivification drift))))))

theorem ay_pcvr_failure_unchecked_vivification
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop) :
    uncheckedVivification ->
    ay_pcvr_VivificationFailure
      literalDeletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedVivification := by
  intro unchecked
  exact ay_pcvr_disj_right literalDeletionMismatch
    (ay_pcvr_Disj missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))))
    (ay_pcvr_disj_right missingCoverage
      (ay_pcvr_Disj representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)))))
      (ay_pcvr_disj_right representativeMismatch
        (ay_pcvr_Disj brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))))
        (ay_pcvr_disj_right brokenReconstruction
          (ay_pcvr_Disj digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)))
          (ay_pcvr_disj_right digestMismatch
            (ay_pcvr_Disj replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification))
            (ay_pcvr_disj_right replayRejected
              (ay_pcvr_Disj fingerprintDrift uncheckedVivification)
              (ay_pcvr_disj_right fingerprintDrift uncheckedVivification
                unchecked))))))

theorem ay_pcvr_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcvr_DiagnosticVivificationLogEntry
      previousLog nextLog currentCnf literalDeletionMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedVivification recompute diagnostic ->
    ay_pcvr_VivificationFailure
      literalDeletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedVivification := by
  intro entry
  exact entry
    (ay_pcvr_VivificationFailure
      literalDeletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedVivification)
    (fun _previous rest1 =>
      rest1
        (ay_pcvr_VivificationFailure
          literalDeletionMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedVivification)
        (fun body _next =>
          body
            (ay_pcvr_VivificationFailure
              literalDeletionMismatch missingCoverage representativeMismatch
              brokenReconstruction digestMismatch replayRejected fingerprintDrift
              uncheckedVivification)
            (fun failure _tail => failure)))

theorem ay_pcvr_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcvr_DiagnosticVivificationLogEntry
      previousLog nextLog currentCnf literalDeletionMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedVivification recompute diagnostic ->
    ay_pcvr_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_pcvr_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_pcvr_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_pcvr_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_pcvr_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_pcvr_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pcvr_DiagnosticVivificationLogEntry
      previousLog nextLog currentCnf literalDeletionMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedVivification recompute diagnostic ->
    ay_pcvr_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_pcvr_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_pcvr_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_pcvr_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_pcvr_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_pcvr_unchecked_vivification_no_public_blessing
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop)
    (diagnostic : Prop) :
    uncheckedVivification ->
    diagnostic ->
    ay_pcvr_NoSemanticClaim diagnostic := by
  intro _unchecked diag
  exact diag

theorem ay_pcvr_failure_no_claim
    (literalDeletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedVivification : Prop)
    (diagnostic : Prop) :
    ay_pcvr_VivificationFailure
      literalDeletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedVivification ->
    diagnostic ->
    ay_pcvr_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
