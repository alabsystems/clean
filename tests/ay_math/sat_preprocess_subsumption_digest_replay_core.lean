-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Subsumption digest replay soundness for preprocessing. The
-- propositions stand for replayable clause coverage, subsumption witnesses, representative-map
-- agreement, model/proof reconstruction, digest membership, checker replay,
-- original fingerprint agreement, diagnostics, and public SAT/UNSAT reports.

def ay_psdr_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_psdr_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_psdr_Equisat (before : Prop) (after : Prop) :=
  ay_psdr_Conj (before -> after) (after -> before)

def ay_psdr_Sat (cnf : Prop) (model : Prop) :=
  ay_psdr_Conj cnf model

def ay_psdr_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_psdr_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_psdr_Conj (leftId -> rightId) (rightId -> leftId)

def ay_psdr_ClauseCoverage
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop) :=
  ay_psdr_Conj coverageWitness
    (deletedClauses -> coveredClauses)

def ay_psdr_RepresentativeAgreement
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop) :=
  ay_psdr_Conj representativeWitness
    (ay_psdr_IdMatch oldRepresentative newRepresentative)

def ay_psdr_ModelReconstruction
    (residualCnf : Prop) (originalCnf : Prop)
    (residualModel : Prop) (originalModel : Prop) :=
  ay_psdr_Sat residualCnf residualModel ->
    ay_psdr_Sat originalCnf originalModel

def ay_psdr_ProofReconstruction
    (originalCnf : Prop) (residualCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_psdr_Replay residualCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_psdr_DigestMembership
    (subsumptionDigest : Prop) (manifestDigest : Prop) :=
  ay_psdr_Conj subsumptionDigest manifestDigest

def ay_psdr_CheckerReplay
    (subsumptionCertificate : Prop) (checkerAccepted : Prop) :=
  ay_psdr_Conj subsumptionCertificate checkerAccepted

def ay_psdr_FingerprintAgreement
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_psdr_Conj fingerprintWitness
    (ay_psdr_IdMatch originalFingerprint residualFingerprint)

def ay_psdr_AcceptedSubsumptionReplay
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_psdr_Conj
    (ay_psdr_ClauseCoverage
      deletedClauses coveredClauses coverageWitness)
    (ay_psdr_Conj
      (ay_psdr_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_psdr_Conj
        (ay_psdr_Equisat originalCnf residualCnf)
        (ay_psdr_Conj
          (ay_psdr_ModelReconstruction
            residualCnf originalCnf residualModel originalModel)
          (ay_psdr_Conj
            (ay_psdr_ProofReconstruction
              originalCnf residualCnf certificate conflict)
            (ay_psdr_Conj
              (ay_psdr_DigestMembership subsumptionDigest manifestDigest)
              (ay_psdr_Conj
                (ay_psdr_CheckerReplay
                  subsumptionCertificate checkerAccepted)
                (ay_psdr_FingerprintAgreement
                  originalFingerprint residualFingerprint
                  fingerprintWitness)))))))

def ay_psdr_AcceptedSubsumptionLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_psdr_Conj previousLog
    (ay_psdr_Conj
      (ay_psdr_AcceptedSubsumptionReplay
        originalCnf residualCnf deletedClauses coveredClauses
        coverageWitness oldRepresentative newRepresentative
        representativeWitness residualModel originalModel certificate conflict
        subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
        originalFingerprint residualFingerprint fingerprintWitness)
      nextLog)

def ay_psdr_SubsumptionFailure
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop) :=
  ay_psdr_Disj deletionMismatch
    (ay_psdr_Disj missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))))

def ay_psdr_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_psdr_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_psdr_Conj currentCnf recompute

def ay_psdr_DiagnosticSubsumptionLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_psdr_Conj previousLog
    (ay_psdr_Conj
      (ay_psdr_Conj
        (ay_psdr_SubsumptionFailure
          deletionMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedSubsumption)
        (ay_psdr_Conj
          (ay_psdr_RecomputeObligation currentCnf recompute)
          (ay_psdr_NoSemanticClaim diagnostic)))
      nextLog)

def ay_psdr_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_psdr_Conj exitCode claim

def ay_psdr_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_psdr_Disj
    (ay_psdr_ExitCodeSound exitCode (ay_psdr_Sat originalCnf model))
    (ay_psdr_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_psdr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_psdr_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_psdr_conj_left
    (left : Prop) (right : Prop) :
    ay_psdr_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_psdr_conj_right
    (left : Prop) (right : Prop) :
    ay_psdr_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_psdr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_psdr_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_psdr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_psdr_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_psdr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_psdr_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_psdr_conj_left (before -> after) (after -> before) eq

theorem ay_psdr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_psdr_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_psdr_conj_right (before -> after) (after -> before) eq

theorem ay_psdr_subsumption_clause_coverage
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_psdr_AcceptedSubsumptionReplay
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_psdr_ClauseCoverage deletedClauses coveredClauses coverageWitness := by
  intro accepted
  exact ay_psdr_conj_left
    (ay_psdr_ClauseCoverage deletedClauses coveredClauses coverageWitness)
    (ay_psdr_Conj
      (ay_psdr_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_psdr_Conj
        (ay_psdr_Equisat originalCnf residualCnf)
        (ay_psdr_Conj
          (ay_psdr_ModelReconstruction
            residualCnf originalCnf residualModel originalModel)
          (ay_psdr_Conj
            (ay_psdr_ProofReconstruction
              originalCnf residualCnf certificate conflict)
            (ay_psdr_Conj
              (ay_psdr_DigestMembership subsumptionDigest manifestDigest)
              (ay_psdr_Conj
                (ay_psdr_CheckerReplay subsumptionCertificate checkerAccepted)
                (ay_psdr_FingerprintAgreement
                  originalFingerprint residualFingerprint
                  fingerprintWitness)))))))
    accepted

theorem ay_psdr_subsumption_representative
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_psdr_AcceptedSubsumptionReplay
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_psdr_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness := by
  intro accepted
  exact accepted
    (ay_psdr_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_psdr_RepresentativeAgreement
          oldRepresentative newRepresentative representativeWitness)
        (fun rep _tail => rep))

theorem ay_psdr_subsumption_equisat
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_psdr_AcceptedSubsumptionReplay
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_psdr_Equisat originalCnf residualCnf := by
  intro accepted
  exact accepted
    (ay_psdr_Equisat originalCnf residualCnf)
    (fun _coverage rest1 =>
      rest1
        (ay_psdr_Equisat originalCnf residualCnf)
        (fun _rep rest2 =>
          rest2
            (ay_psdr_Equisat originalCnf residualCnf)
            (fun eq _tail => eq)))

theorem ay_psdr_subsumption_model_reconstruction
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_psdr_AcceptedSubsumptionReplay
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_psdr_ModelReconstruction residualCnf originalCnf residualModel
      originalModel := by
  intro accepted
  exact accepted
    (ay_psdr_ModelReconstruction
      residualCnf originalCnf residualModel originalModel)
    (fun _coverage rest1 =>
      rest1
        (ay_psdr_ModelReconstruction
          residualCnf originalCnf residualModel originalModel)
        (fun _rep rest2 =>
          rest2
            (ay_psdr_ModelReconstruction
              residualCnf originalCnf residualModel originalModel)
            (fun _eq rest3 =>
              rest3
                (ay_psdr_ModelReconstruction
                  residualCnf originalCnf residualModel originalModel)
                (fun model _tail => model))))

theorem ay_psdr_subsumption_proof_reconstruction
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_psdr_AcceptedSubsumptionReplay
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_psdr_ProofReconstruction originalCnf residualCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_psdr_ProofReconstruction originalCnf residualCnf certificate conflict)
    (fun _coverage rest1 =>
      rest1
        (ay_psdr_ProofReconstruction originalCnf residualCnf certificate conflict)
        (fun _rep rest2 =>
          rest2
            (ay_psdr_ProofReconstruction
              originalCnf residualCnf certificate conflict)
            (fun _eq rest3 =>
              rest3
                (ay_psdr_ProofReconstruction
                  originalCnf residualCnf certificate conflict)
                (fun _model rest4 =>
                  rest4
                    (ay_psdr_ProofReconstruction
                      originalCnf residualCnf certificate conflict)
                    (fun proof _tail => proof)))))

theorem ay_psdr_subsumption_digest
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_psdr_AcceptedSubsumptionReplay
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_psdr_DigestMembership subsumptionDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_psdr_DigestMembership subsumptionDigest manifestDigest)
    (fun _coverage rest1 =>
      rest1
        (ay_psdr_DigestMembership subsumptionDigest manifestDigest)
        (fun _rep rest2 =>
          rest2
            (ay_psdr_DigestMembership subsumptionDigest manifestDigest)
            (fun _eq rest3 =>
              rest3
                (ay_psdr_DigestMembership subsumptionDigest manifestDigest)
                (fun _model rest4 =>
                  rest4
                    (ay_psdr_DigestMembership subsumptionDigest manifestDigest)
                    (fun _proof rest5 =>
                      rest5
                        (ay_psdr_DigestMembership subsumptionDigest manifestDigest)
                        (fun digest _tail => digest))))))

theorem ay_psdr_subsumption_checker
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_psdr_AcceptedSubsumptionReplay
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_psdr_CheckerReplay subsumptionCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_psdr_CheckerReplay subsumptionCertificate checkerAccepted)
    (fun _coverage rest1 =>
      rest1
        (ay_psdr_CheckerReplay subsumptionCertificate checkerAccepted)
        (fun _rep rest2 =>
          rest2
            (ay_psdr_CheckerReplay subsumptionCertificate checkerAccepted)
            (fun _eq rest3 =>
              rest3
                (ay_psdr_CheckerReplay subsumptionCertificate checkerAccepted)
                (fun _model rest4 =>
                  rest4
                    (ay_psdr_CheckerReplay subsumptionCertificate checkerAccepted)
                    (fun _proof rest5 =>
                      rest5
                        (ay_psdr_CheckerReplay
                          subsumptionCertificate checkerAccepted)
                        (fun _digest rest6 =>
                          rest6
                            (ay_psdr_CheckerReplay
                              subsumptionCertificate checkerAccepted)
                            (fun checker _tail => checker)))))))

theorem ay_psdr_subsumption_fingerprint
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_psdr_AcceptedSubsumptionReplay
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_psdr_FingerprintAgreement
      originalFingerprint residualFingerprint fingerprintWitness := by
  intro accepted
  exact accepted
    (ay_psdr_FingerprintAgreement
      originalFingerprint residualFingerprint fingerprintWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_psdr_FingerprintAgreement
          originalFingerprint residualFingerprint fingerprintWitness)
        (fun _rep rest2 =>
          rest2
            (ay_psdr_FingerprintAgreement
              originalFingerprint residualFingerprint fingerprintWitness)
            (fun _eq rest3 =>
              rest3
                (ay_psdr_FingerprintAgreement
                  originalFingerprint residualFingerprint fingerprintWitness)
                (fun _model rest4 =>
                  rest4
                    (ay_psdr_FingerprintAgreement
                      originalFingerprint residualFingerprint fingerprintWitness)
                    (fun _proof rest5 =>
                      rest5
                        (ay_psdr_FingerprintAgreement
                          originalFingerprint residualFingerprint
                          fingerprintWitness)
                        (fun _digest rest6 =>
                          rest6
                            (ay_psdr_FingerprintAgreement
                              originalFingerprint residualFingerprint
                              fingerprintWitness)
                            (fun _checker fp => fp)))))))

theorem ay_psdr_sat_pullback
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_psdr_AcceptedSubsumptionReplay
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_psdr_Sat residualCnf residualModel ->
    ay_psdr_Sat originalCnf originalModel := by
  intro accepted residualSat
  exact
    (ay_psdr_subsumption_model_reconstruction
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative representativeWitness
      residualModel originalModel certificate conflict subsumptionDigest
      manifestDigest subsumptionCertificate checkerAccepted originalFingerprint
      residualFingerprint fingerprintWitness accepted)
      residualSat

theorem ay_psdr_unsat_pushback
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_psdr_AcceptedSubsumptionReplay
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_psdr_Replay residualCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay cert original
  exact
    (ay_psdr_subsumption_proof_reconstruction
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative representativeWitness
      residualModel originalModel certificate conflict subsumptionDigest
      manifestDigest subsumptionCertificate checkerAccepted originalFingerprint
      residualFingerprint fingerprintWitness accepted)
      replay cert original

theorem ay_psdr_public_sat
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_psdr_AcceptedSubsumptionReplay
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_psdr_Sat residualCnf residualModel ->
    exitCode ->
    ay_psdr_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted residualSat exit
  exact ay_psdr_disj_left
    (ay_psdr_ExitCodeSound exitCode (ay_psdr_Sat originalCnf originalModel))
    (ay_psdr_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_psdr_conj_intro exitCode
      (ay_psdr_Sat originalCnf originalModel)
      exit
      (ay_psdr_sat_pullback
        originalCnf residualCnf deletedClauses coveredClauses
        coverageWitness oldRepresentative newRepresentative representativeWitness
        residualModel originalModel certificate conflict subsumptionDigest
        manifestDigest subsumptionCertificate checkerAccepted originalFingerprint
        residualFingerprint fingerprintWitness accepted residualSat))

theorem ay_psdr_public_unsat
    (originalCnf : Prop) (residualCnf : Prop)
    (deletedClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (residualModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (subsumptionDigest : Prop) (manifestDigest : Prop)
    (subsumptionCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (residualFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_psdr_AcceptedSubsumptionReplay
      originalCnf residualCnf deletedClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness residualModel originalModel certificate conflict
      subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
      originalFingerprint residualFingerprint fingerprintWitness ->
    ay_psdr_Replay residualCnf certificate conflict ->
    exitCode ->
    ay_psdr_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_psdr_disj_right
    (ay_psdr_ExitCodeSound exitCode (ay_psdr_Sat originalCnf originalModel))
    (ay_psdr_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_psdr_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      exit
      (fun cert original =>
        ay_psdr_unsat_pushback
          originalCnf residualCnf deletedClauses coveredClauses
          coverageWitness oldRepresentative newRepresentative
          representativeWitness residualModel originalModel certificate conflict
          subsumptionDigest manifestDigest subsumptionCertificate checkerAccepted
          originalFingerprint residualFingerprint fingerprintWitness accepted
          replay cert original))

theorem ay_psdr_failure_deletion_mismatch
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop) :
    deletionMismatch ->
    ay_psdr_SubsumptionFailure
      deletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedSubsumption := by
  intro mismatch
  exact ay_psdr_disj_left deletionMismatch
    (ay_psdr_Disj missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))))
    mismatch

theorem ay_psdr_failure_missing_coverage
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop) :
    missingCoverage ->
    ay_psdr_SubsumptionFailure
      deletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedSubsumption := by
  intro missing
  exact ay_psdr_disj_right deletionMismatch
    (ay_psdr_Disj missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))))
    (ay_psdr_disj_left missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)))))
      missing)

theorem ay_psdr_failure_representative_mismatch
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop) :
    representativeMismatch ->
    ay_psdr_SubsumptionFailure
      deletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedSubsumption := by
  intro mismatch
  exact ay_psdr_disj_right deletionMismatch
    (ay_psdr_Disj missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))))
    (ay_psdr_disj_right missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)))))
      (ay_psdr_disj_left representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))
        mismatch))

theorem ay_psdr_failure_broken_reconstruction
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop) :
    brokenReconstruction ->
    ay_psdr_SubsumptionFailure
      deletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedSubsumption := by
  intro broken
  exact ay_psdr_disj_right deletionMismatch
    (ay_psdr_Disj missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))))
    (ay_psdr_disj_right missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)))))
      (ay_psdr_disj_right representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))
        (ay_psdr_disj_left brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)))
          broken)))

theorem ay_psdr_failure_digest_mismatch
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop) :
    digestMismatch ->
    ay_psdr_SubsumptionFailure
      deletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedSubsumption := by
  intro mismatch
  exact ay_psdr_disj_right deletionMismatch
    (ay_psdr_Disj missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))))
    (ay_psdr_disj_right missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)))))
      (ay_psdr_disj_right representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))
        (ay_psdr_disj_right brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)))
          (ay_psdr_disj_left digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))
            mismatch))))

theorem ay_psdr_failure_replay_rejected
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop) :
    replayRejected ->
    ay_psdr_SubsumptionFailure
      deletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedSubsumption := by
  intro rejected
  exact ay_psdr_disj_right deletionMismatch
    (ay_psdr_Disj missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))))
    (ay_psdr_disj_right missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)))))
      (ay_psdr_disj_right representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))
        (ay_psdr_disj_right brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)))
          (ay_psdr_disj_right digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))
            (ay_psdr_disj_left replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)
              rejected)))))

theorem ay_psdr_failure_fingerprint_drift
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop) :
    fingerprintDrift ->
    ay_psdr_SubsumptionFailure
      deletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedSubsumption := by
  intro drift
  exact ay_psdr_disj_right deletionMismatch
    (ay_psdr_Disj missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))))
    (ay_psdr_disj_right missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)))))
      (ay_psdr_disj_right representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))
        (ay_psdr_disj_right brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)))
          (ay_psdr_disj_right digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))
            (ay_psdr_disj_right replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)
              (ay_psdr_disj_left fingerprintDrift uncheckedSubsumption drift))))))

theorem ay_psdr_failure_unchecked_subsumption
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop) :
    uncheckedSubsumption ->
    ay_psdr_SubsumptionFailure
      deletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedSubsumption := by
  intro unchecked
  exact ay_psdr_disj_right deletionMismatch
    (ay_psdr_Disj missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))))
    (ay_psdr_disj_right missingCoverage
      (ay_psdr_Disj representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)))))
      (ay_psdr_disj_right representativeMismatch
        (ay_psdr_Disj brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))))
        (ay_psdr_disj_right brokenReconstruction
          (ay_psdr_Disj digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)))
          (ay_psdr_disj_right digestMismatch
            (ay_psdr_Disj replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption))
            (ay_psdr_disj_right replayRejected
              (ay_psdr_Disj fingerprintDrift uncheckedSubsumption)
              (ay_psdr_disj_right fingerprintDrift uncheckedSubsumption
                unchecked))))))

theorem ay_psdr_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_psdr_DiagnosticSubsumptionLogEntry
      previousLog nextLog currentCnf deletionMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedSubsumption recompute diagnostic ->
    ay_psdr_SubsumptionFailure
      deletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedSubsumption := by
  intro entry
  exact entry
    (ay_psdr_SubsumptionFailure
      deletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedSubsumption)
    (fun _previous rest1 =>
      rest1
        (ay_psdr_SubsumptionFailure
          deletionMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedSubsumption)
        (fun body _next =>
          body
            (ay_psdr_SubsumptionFailure
              deletionMismatch missingCoverage representativeMismatch
              brokenReconstruction digestMismatch replayRejected fingerprintDrift
              uncheckedSubsumption)
            (fun failure _tail => failure)))

theorem ay_psdr_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_psdr_DiagnosticSubsumptionLogEntry
      previousLog nextLog currentCnf deletionMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedSubsumption recompute diagnostic ->
    ay_psdr_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_psdr_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_psdr_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_psdr_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_psdr_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_psdr_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_psdr_DiagnosticSubsumptionLogEntry
      previousLog nextLog currentCnf deletionMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedSubsumption recompute diagnostic ->
    ay_psdr_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_psdr_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_psdr_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_psdr_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_psdr_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_psdr_unchecked_subsumption_no_public_blessing
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop)
    (diagnostic : Prop) :
    uncheckedSubsumption ->
    diagnostic ->
    ay_psdr_NoSemanticClaim diagnostic := by
  intro _unchecked diag
  exact diag

theorem ay_psdr_failure_no_claim
    (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedSubsumption : Prop)
    (diagnostic : Prop) :
    ay_psdr_SubsumptionFailure
      deletionMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedSubsumption ->
    diagnostic ->
    ay_psdr_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
