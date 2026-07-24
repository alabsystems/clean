-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Hyper-binary resolution replay soundness for preprocessing. The
-- propositions stand for accepted HBR trace and implication coverage, representative-map
-- agreement, model/proof reconstruction, digest membership, checker replay,
-- original fingerprint agreement, diagnostics, and public SAT/UNSAT reports.

def ay_phbr_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_phbr_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_phbr_Equisat (before : Prop) (after : Prop) :=
  ay_phbr_Conj (before -> after) (after -> before)

def ay_phbr_Sat (cnf : Prop) (model : Prop) :=
  ay_phbr_Conj cnf model

def ay_phbr_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_phbr_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_phbr_Conj (leftId -> rightId) (rightId -> leftId)

def ay_phbr_ClauseCoverage
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop) :=
  ay_phbr_Conj coverageWitness
    (implicationTrace -> coveredImplications)

def ay_phbr_RepresentativeAgreement
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop) :=
  ay_phbr_Conj representativeWitness
    (ay_phbr_IdMatch oldRepresentative newRepresentative)

def ay_phbr_ModelReconstruction
    (hbrCnf : Prop) (originalCnf : Prop)
    (hbrModel : Prop) (originalModel : Prop) :=
  ay_phbr_Sat hbrCnf hbrModel ->
    ay_phbr_Sat originalCnf originalModel

def ay_phbr_ProofReconstruction
    (originalCnf : Prop) (hbrCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_phbr_Replay hbrCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_phbr_DigestMembership
    (hbrDigest : Prop) (manifestDigest : Prop) :=
  ay_phbr_Conj hbrDigest manifestDigest

def ay_phbr_CheckerReplay
    (hbrCertificate : Prop) (checkerAccepted : Prop) :=
  ay_phbr_Conj hbrCertificate checkerAccepted

def ay_phbr_FingerprintAgreement
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_phbr_Conj fingerprintWitness
    (ay_phbr_IdMatch originalFingerprint hbrFingerprint)

def ay_phbr_AcceptedHbrReplay
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_phbr_Conj
    (ay_phbr_ClauseCoverage
      implicationTrace coveredImplications coverageWitness)
    (ay_phbr_Conj
      (ay_phbr_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_phbr_Conj
        (ay_phbr_Equisat originalCnf hbrCnf)
        (ay_phbr_Conj
          (ay_phbr_ModelReconstruction
            hbrCnf originalCnf hbrModel originalModel)
          (ay_phbr_Conj
            (ay_phbr_ProofReconstruction
              originalCnf hbrCnf certificate conflict)
            (ay_phbr_Conj
              (ay_phbr_DigestMembership hbrDigest manifestDigest)
              (ay_phbr_Conj
                (ay_phbr_CheckerReplay
                  hbrCertificate checkerAccepted)
                (ay_phbr_FingerprintAgreement
                  originalFingerprint hbrFingerprint
                  fingerprintWitness)))))))

def ay_phbr_AcceptedHbrLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_phbr_Conj previousLog
    (ay_phbr_Conj
      (ay_phbr_AcceptedHbrReplay
        originalCnf hbrCnf implicationTrace coveredImplications
        coverageWitness oldRepresentative newRepresentative
        representativeWitness hbrModel originalModel certificate conflict
        hbrDigest manifestDigest hbrCertificate checkerAccepted
        originalFingerprint hbrFingerprint fingerprintWitness)
      nextLog)

def ay_phbr_HbrFailure
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop) :=
  ay_phbr_Disj impliedBinaryMismatch
    (ay_phbr_Disj missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))))

def ay_phbr_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_phbr_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_phbr_Conj currentCnf recompute

def ay_phbr_DiagnosticHbrLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_phbr_Conj previousLog
    (ay_phbr_Conj
      (ay_phbr_Conj
        (ay_phbr_HbrFailure
          impliedBinaryMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedHbr)
        (ay_phbr_Conj
          (ay_phbr_RecomputeObligation currentCnf recompute)
          (ay_phbr_NoSemanticClaim diagnostic)))
      nextLog)

def ay_phbr_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_phbr_Conj exitCode claim

def ay_phbr_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_phbr_Disj
    (ay_phbr_ExitCodeSound exitCode (ay_phbr_Sat originalCnf model))
    (ay_phbr_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_phbr_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_phbr_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_phbr_conj_left
    (left : Prop) (right : Prop) :
    ay_phbr_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_phbr_conj_right
    (left : Prop) (right : Prop) :
    ay_phbr_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_phbr_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_phbr_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_phbr_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_phbr_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_phbr_equisat_forward
    (before : Prop) (after : Prop) :
    ay_phbr_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_phbr_conj_left (before -> after) (after -> before) eq

theorem ay_phbr_equisat_backward
    (before : Prop) (after : Prop) :
    ay_phbr_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_phbr_conj_right (before -> after) (after -> before) eq

theorem ay_phbr_hbr_implication_coverage
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_phbr_AcceptedHbrReplay
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness hbrModel originalModel certificate conflict
      hbrDigest manifestDigest hbrCertificate checkerAccepted
      originalFingerprint hbrFingerprint fingerprintWitness ->
    ay_phbr_ClauseCoverage implicationTrace coveredImplications coverageWitness := by
  intro accepted
  exact ay_phbr_conj_left
    (ay_phbr_ClauseCoverage implicationTrace coveredImplications coverageWitness)
    (ay_phbr_Conj
      (ay_phbr_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_phbr_Conj
        (ay_phbr_Equisat originalCnf hbrCnf)
        (ay_phbr_Conj
          (ay_phbr_ModelReconstruction
            hbrCnf originalCnf hbrModel originalModel)
          (ay_phbr_Conj
            (ay_phbr_ProofReconstruction
              originalCnf hbrCnf certificate conflict)
            (ay_phbr_Conj
              (ay_phbr_DigestMembership hbrDigest manifestDigest)
              (ay_phbr_Conj
                (ay_phbr_CheckerReplay hbrCertificate checkerAccepted)
                (ay_phbr_FingerprintAgreement
                  originalFingerprint hbrFingerprint
                  fingerprintWitness)))))))
    accepted

theorem ay_phbr_hbr_representative
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_phbr_AcceptedHbrReplay
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness hbrModel originalModel certificate conflict
      hbrDigest manifestDigest hbrCertificate checkerAccepted
      originalFingerprint hbrFingerprint fingerprintWitness ->
    ay_phbr_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness := by
  intro accepted
  exact accepted
    (ay_phbr_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_phbr_RepresentativeAgreement
          oldRepresentative newRepresentative representativeWitness)
        (fun rep _tail => rep))

theorem ay_phbr_hbr_equisat
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_phbr_AcceptedHbrReplay
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness hbrModel originalModel certificate conflict
      hbrDigest manifestDigest hbrCertificate checkerAccepted
      originalFingerprint hbrFingerprint fingerprintWitness ->
    ay_phbr_Equisat originalCnf hbrCnf := by
  intro accepted
  exact accepted
    (ay_phbr_Equisat originalCnf hbrCnf)
    (fun _coverage rest1 =>
      rest1
        (ay_phbr_Equisat originalCnf hbrCnf)
        (fun _rep rest2 =>
          rest2
            (ay_phbr_Equisat originalCnf hbrCnf)
            (fun eq _tail => eq)))

theorem ay_phbr_hbr_model_reconstruction
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_phbr_AcceptedHbrReplay
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness hbrModel originalModel certificate conflict
      hbrDigest manifestDigest hbrCertificate checkerAccepted
      originalFingerprint hbrFingerprint fingerprintWitness ->
    ay_phbr_ModelReconstruction hbrCnf originalCnf hbrModel
      originalModel := by
  intro accepted
  exact accepted
    (ay_phbr_ModelReconstruction
      hbrCnf originalCnf hbrModel originalModel)
    (fun _coverage rest1 =>
      rest1
        (ay_phbr_ModelReconstruction
          hbrCnf originalCnf hbrModel originalModel)
        (fun _rep rest2 =>
          rest2
            (ay_phbr_ModelReconstruction
              hbrCnf originalCnf hbrModel originalModel)
            (fun _eq rest3 =>
              rest3
                (ay_phbr_ModelReconstruction
                  hbrCnf originalCnf hbrModel originalModel)
                (fun model _tail => model))))

theorem ay_phbr_hbr_proof_reconstruction
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_phbr_AcceptedHbrReplay
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness hbrModel originalModel certificate conflict
      hbrDigest manifestDigest hbrCertificate checkerAccepted
      originalFingerprint hbrFingerprint fingerprintWitness ->
    ay_phbr_ProofReconstruction originalCnf hbrCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_phbr_ProofReconstruction originalCnf hbrCnf certificate conflict)
    (fun _coverage rest1 =>
      rest1
        (ay_phbr_ProofReconstruction originalCnf hbrCnf certificate conflict)
        (fun _rep rest2 =>
          rest2
            (ay_phbr_ProofReconstruction
              originalCnf hbrCnf certificate conflict)
            (fun _eq rest3 =>
              rest3
                (ay_phbr_ProofReconstruction
                  originalCnf hbrCnf certificate conflict)
                (fun _model rest4 =>
                  rest4
                    (ay_phbr_ProofReconstruction
                      originalCnf hbrCnf certificate conflict)
                    (fun proof _tail => proof)))))

theorem ay_phbr_hbr_digest
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_phbr_AcceptedHbrReplay
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness hbrModel originalModel certificate conflict
      hbrDigest manifestDigest hbrCertificate checkerAccepted
      originalFingerprint hbrFingerprint fingerprintWitness ->
    ay_phbr_DigestMembership hbrDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_phbr_DigestMembership hbrDigest manifestDigest)
    (fun _coverage rest1 =>
      rest1
        (ay_phbr_DigestMembership hbrDigest manifestDigest)
        (fun _rep rest2 =>
          rest2
            (ay_phbr_DigestMembership hbrDigest manifestDigest)
            (fun _eq rest3 =>
              rest3
                (ay_phbr_DigestMembership hbrDigest manifestDigest)
                (fun _model rest4 =>
                  rest4
                    (ay_phbr_DigestMembership hbrDigest manifestDigest)
                    (fun _proof rest5 =>
                      rest5
                        (ay_phbr_DigestMembership hbrDigest manifestDigest)
                        (fun digest _tail => digest))))))

theorem ay_phbr_hbr_checker
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_phbr_AcceptedHbrReplay
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness hbrModel originalModel certificate conflict
      hbrDigest manifestDigest hbrCertificate checkerAccepted
      originalFingerprint hbrFingerprint fingerprintWitness ->
    ay_phbr_CheckerReplay hbrCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_phbr_CheckerReplay hbrCertificate checkerAccepted)
    (fun _coverage rest1 =>
      rest1
        (ay_phbr_CheckerReplay hbrCertificate checkerAccepted)
        (fun _rep rest2 =>
          rest2
            (ay_phbr_CheckerReplay hbrCertificate checkerAccepted)
            (fun _eq rest3 =>
              rest3
                (ay_phbr_CheckerReplay hbrCertificate checkerAccepted)
                (fun _model rest4 =>
                  rest4
                    (ay_phbr_CheckerReplay hbrCertificate checkerAccepted)
                    (fun _proof rest5 =>
                      rest5
                        (ay_phbr_CheckerReplay
                          hbrCertificate checkerAccepted)
                        (fun _digest rest6 =>
                          rest6
                            (ay_phbr_CheckerReplay
                              hbrCertificate checkerAccepted)
                            (fun checker _tail => checker)))))))

theorem ay_phbr_hbr_fingerprint
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_phbr_AcceptedHbrReplay
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness hbrModel originalModel certificate conflict
      hbrDigest manifestDigest hbrCertificate checkerAccepted
      originalFingerprint hbrFingerprint fingerprintWitness ->
    ay_phbr_FingerprintAgreement
      originalFingerprint hbrFingerprint fingerprintWitness := by
  intro accepted
  exact accepted
    (ay_phbr_FingerprintAgreement
      originalFingerprint hbrFingerprint fingerprintWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_phbr_FingerprintAgreement
          originalFingerprint hbrFingerprint fingerprintWitness)
        (fun _rep rest2 =>
          rest2
            (ay_phbr_FingerprintAgreement
              originalFingerprint hbrFingerprint fingerprintWitness)
            (fun _eq rest3 =>
              rest3
                (ay_phbr_FingerprintAgreement
                  originalFingerprint hbrFingerprint fingerprintWitness)
                (fun _model rest4 =>
                  rest4
                    (ay_phbr_FingerprintAgreement
                      originalFingerprint hbrFingerprint fingerprintWitness)
                    (fun _proof rest5 =>
                      rest5
                        (ay_phbr_FingerprintAgreement
                          originalFingerprint hbrFingerprint
                          fingerprintWitness)
                        (fun _digest rest6 =>
                          rest6
                            (ay_phbr_FingerprintAgreement
                              originalFingerprint hbrFingerprint
                              fingerprintWitness)
                            (fun _checker fp => fp)))))))

theorem ay_phbr_sat_pullback
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_phbr_AcceptedHbrReplay
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness hbrModel originalModel certificate conflict
      hbrDigest manifestDigest hbrCertificate checkerAccepted
      originalFingerprint hbrFingerprint fingerprintWitness ->
    ay_phbr_Sat hbrCnf hbrModel ->
    ay_phbr_Sat originalCnf originalModel := by
  intro accepted hbrSat
  exact
    (ay_phbr_hbr_model_reconstruction
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative representativeWitness
      hbrModel originalModel certificate conflict hbrDigest
      manifestDigest hbrCertificate checkerAccepted originalFingerprint
      hbrFingerprint fingerprintWitness accepted)
      hbrSat

theorem ay_phbr_unsat_pushback
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_phbr_AcceptedHbrReplay
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness hbrModel originalModel certificate conflict
      hbrDigest manifestDigest hbrCertificate checkerAccepted
      originalFingerprint hbrFingerprint fingerprintWitness ->
    ay_phbr_Replay hbrCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay cert original
  exact
    (ay_phbr_hbr_proof_reconstruction
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative representativeWitness
      hbrModel originalModel certificate conflict hbrDigest
      manifestDigest hbrCertificate checkerAccepted originalFingerprint
      hbrFingerprint fingerprintWitness accepted)
      replay cert original

theorem ay_phbr_public_sat
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_phbr_AcceptedHbrReplay
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness hbrModel originalModel certificate conflict
      hbrDigest manifestDigest hbrCertificate checkerAccepted
      originalFingerprint hbrFingerprint fingerprintWitness ->
    ay_phbr_Sat hbrCnf hbrModel ->
    exitCode ->
    ay_phbr_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted hbrSat exit
  exact ay_phbr_disj_left
    (ay_phbr_ExitCodeSound exitCode (ay_phbr_Sat originalCnf originalModel))
    (ay_phbr_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_phbr_conj_intro exitCode
      (ay_phbr_Sat originalCnf originalModel)
      exit
      (ay_phbr_sat_pullback
        originalCnf hbrCnf implicationTrace coveredImplications
        coverageWitness oldRepresentative newRepresentative representativeWitness
        hbrModel originalModel certificate conflict hbrDigest
        manifestDigest hbrCertificate checkerAccepted originalFingerprint
        hbrFingerprint fingerprintWitness accepted hbrSat))

theorem ay_phbr_public_unsat
    (originalCnf : Prop) (hbrCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (hbrModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (hbrDigest : Prop) (manifestDigest : Prop)
    (hbrCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (hbrFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_phbr_AcceptedHbrReplay
      originalCnf hbrCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness hbrModel originalModel certificate conflict
      hbrDigest manifestDigest hbrCertificate checkerAccepted
      originalFingerprint hbrFingerprint fingerprintWitness ->
    ay_phbr_Replay hbrCnf certificate conflict ->
    exitCode ->
    ay_phbr_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_phbr_disj_right
    (ay_phbr_ExitCodeSound exitCode (ay_phbr_Sat originalCnf originalModel))
    (ay_phbr_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_phbr_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      exit
      (fun cert original =>
        ay_phbr_unsat_pushback
          originalCnf hbrCnf implicationTrace coveredImplications
          coverageWitness oldRepresentative newRepresentative
          representativeWitness hbrModel originalModel certificate conflict
          hbrDigest manifestDigest hbrCertificate checkerAccepted
          originalFingerprint hbrFingerprint fingerprintWitness accepted
          replay cert original))

theorem ay_phbr_failure_implied_binary_mismatch
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop) :
    impliedBinaryMismatch ->
    ay_phbr_HbrFailure
      impliedBinaryMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedHbr := by
  intro mismatch
  exact ay_phbr_disj_left impliedBinaryMismatch
    (ay_phbr_Disj missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))))
    mismatch

theorem ay_phbr_failure_missing_coverage
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop) :
    missingCoverage ->
    ay_phbr_HbrFailure
      impliedBinaryMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedHbr := by
  intro missing
  exact ay_phbr_disj_right impliedBinaryMismatch
    (ay_phbr_Disj missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))))
    (ay_phbr_disj_left missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)))))
      missing)

theorem ay_phbr_failure_representative_mismatch
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop) :
    representativeMismatch ->
    ay_phbr_HbrFailure
      impliedBinaryMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedHbr := by
  intro mismatch
  exact ay_phbr_disj_right impliedBinaryMismatch
    (ay_phbr_Disj missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))))
    (ay_phbr_disj_right missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)))))
      (ay_phbr_disj_left representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))
        mismatch))

theorem ay_phbr_failure_broken_reconstruction
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop) :
    brokenReconstruction ->
    ay_phbr_HbrFailure
      impliedBinaryMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedHbr := by
  intro broken
  exact ay_phbr_disj_right impliedBinaryMismatch
    (ay_phbr_Disj missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))))
    (ay_phbr_disj_right missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)))))
      (ay_phbr_disj_right representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))
        (ay_phbr_disj_left brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)))
          broken)))

theorem ay_phbr_failure_digest_mismatch
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop) :
    digestMismatch ->
    ay_phbr_HbrFailure
      impliedBinaryMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedHbr := by
  intro mismatch
  exact ay_phbr_disj_right impliedBinaryMismatch
    (ay_phbr_Disj missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))))
    (ay_phbr_disj_right missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)))))
      (ay_phbr_disj_right representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))
        (ay_phbr_disj_right brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)))
          (ay_phbr_disj_left digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))
            mismatch))))

theorem ay_phbr_failure_replay_rejected
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop) :
    replayRejected ->
    ay_phbr_HbrFailure
      impliedBinaryMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedHbr := by
  intro rejected
  exact ay_phbr_disj_right impliedBinaryMismatch
    (ay_phbr_Disj missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))))
    (ay_phbr_disj_right missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)))))
      (ay_phbr_disj_right representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))
        (ay_phbr_disj_right brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)))
          (ay_phbr_disj_right digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))
            (ay_phbr_disj_left replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)
              rejected)))))

theorem ay_phbr_failure_fingerprint_drift
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop) :
    fingerprintDrift ->
    ay_phbr_HbrFailure
      impliedBinaryMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedHbr := by
  intro drift
  exact ay_phbr_disj_right impliedBinaryMismatch
    (ay_phbr_Disj missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))))
    (ay_phbr_disj_right missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)))))
      (ay_phbr_disj_right representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))
        (ay_phbr_disj_right brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)))
          (ay_phbr_disj_right digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))
            (ay_phbr_disj_right replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)
              (ay_phbr_disj_left fingerprintDrift uncheckedHbr drift))))))

theorem ay_phbr_failure_unchecked_hbr
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop) :
    uncheckedHbr ->
    ay_phbr_HbrFailure
      impliedBinaryMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedHbr := by
  intro unchecked
  exact ay_phbr_disj_right impliedBinaryMismatch
    (ay_phbr_Disj missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))))
    (ay_phbr_disj_right missingCoverage
      (ay_phbr_Disj representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)))))
      (ay_phbr_disj_right representativeMismatch
        (ay_phbr_Disj brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))))
        (ay_phbr_disj_right brokenReconstruction
          (ay_phbr_Disj digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)))
          (ay_phbr_disj_right digestMismatch
            (ay_phbr_Disj replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr))
            (ay_phbr_disj_right replayRejected
              (ay_phbr_Disj fingerprintDrift uncheckedHbr)
              (ay_phbr_disj_right fingerprintDrift uncheckedHbr
                unchecked))))))

theorem ay_phbr_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_phbr_DiagnosticHbrLogEntry
      previousLog nextLog currentCnf impliedBinaryMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedHbr recompute diagnostic ->
    ay_phbr_HbrFailure
      impliedBinaryMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedHbr := by
  intro entry
  exact entry
    (ay_phbr_HbrFailure
      impliedBinaryMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedHbr)
    (fun _previous rest1 =>
      rest1
        (ay_phbr_HbrFailure
          impliedBinaryMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedHbr)
        (fun body _next =>
          body
            (ay_phbr_HbrFailure
              impliedBinaryMismatch missingCoverage representativeMismatch
              brokenReconstruction digestMismatch replayRejected fingerprintDrift
              uncheckedHbr)
            (fun failure _tail => failure)))

theorem ay_phbr_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_phbr_DiagnosticHbrLogEntry
      previousLog nextLog currentCnf impliedBinaryMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedHbr recompute diagnostic ->
    ay_phbr_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_phbr_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_phbr_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_phbr_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_phbr_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_phbr_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_phbr_DiagnosticHbrLogEntry
      previousLog nextLog currentCnf impliedBinaryMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedHbr recompute diagnostic ->
    ay_phbr_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_phbr_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_phbr_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_phbr_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_phbr_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_phbr_unchecked_hbr_no_public_blessing
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop)
    (diagnostic : Prop) :
    uncheckedHbr ->
    diagnostic ->
    ay_phbr_NoSemanticClaim diagnostic := by
  intro _unchecked diag
  exact diag

theorem ay_phbr_failure_no_claim
    (impliedBinaryMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedHbr : Prop)
    (diagnostic : Prop) :
    ay_phbr_HbrFailure
      impliedBinaryMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedHbr ->
    diagnostic ->
    ay_phbr_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
