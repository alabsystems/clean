-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Duplicate-clause hash replay soundness for preprocessing. The
-- propositions stand for duplicate hash evidence and clause coverage, representative-map
-- agreement, model/proof reconstruction, digest membership, checker replay,
-- original fingerprint agreement, diagnostics, and public SAT/UNSAT reports.

def ay_pdch_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pdch_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pdch_Equisat (before : Prop) (after : Prop) :=
  ay_pdch_Conj (before -> after) (after -> before)

def ay_pdch_Sat (cnf : Prop) (model : Prop) :=
  ay_pdch_Conj cnf model

def ay_pdch_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pdch_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pdch_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pdch_ClauseCoverage
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop) :=
  ay_pdch_Conj coverageWitness
    (duplicateClauses -> coveredClauses)

def ay_pdch_RepresentativeAgreement
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop) :=
  ay_pdch_Conj representativeWitness
    (ay_pdch_IdMatch oldRepresentative newRepresentative)

def ay_pdch_ModelReconstruction
    (deduplicatedCnf : Prop) (originalCnf : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop) :=
  ay_pdch_Sat deduplicatedCnf deduplicatedModel ->
    ay_pdch_Sat originalCnf originalModel

def ay_pdch_ProofReconstruction
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pdch_Replay deduplicatedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pdch_DigestMembership
    (duplicateHashDigest : Prop) (manifestDigest : Prop) :=
  ay_pdch_Conj duplicateHashDigest manifestDigest

def ay_pdch_CheckerReplay
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pdch_Conj duplicateHashCertificate checkerAccepted

def ay_pdch_FingerprintAgreement
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pdch_Conj fingerprintWitness
    (ay_pdch_IdMatch originalFingerprint deduplicatedFingerprint)

def ay_pdch_AcceptedDuplicateHashReplay
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pdch_Conj
    (ay_pdch_ClauseCoverage
      duplicateClauses coveredClauses coverageWitness)
    (ay_pdch_Conj
      (ay_pdch_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_pdch_Conj
        (ay_pdch_Equisat originalCnf deduplicatedCnf)
        (ay_pdch_Conj
          (ay_pdch_ModelReconstruction
            deduplicatedCnf originalCnf deduplicatedModel originalModel)
          (ay_pdch_Conj
            (ay_pdch_ProofReconstruction
              originalCnf deduplicatedCnf certificate conflict)
            (ay_pdch_Conj
              (ay_pdch_DigestMembership duplicateHashDigest manifestDigest)
              (ay_pdch_Conj
                (ay_pdch_CheckerReplay
                  duplicateHashCertificate checkerAccepted)
                (ay_pdch_FingerprintAgreement
                  originalFingerprint deduplicatedFingerprint
                  fingerprintWitness)))))))

def ay_pdch_AcceptedDuplicateHashLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pdch_Conj previousLog
    (ay_pdch_Conj
      (ay_pdch_AcceptedDuplicateHashReplay
        originalCnf deduplicatedCnf duplicateClauses coveredClauses
        coverageWitness oldRepresentative newRepresentative
        representativeWitness deduplicatedModel originalModel certificate conflict
        duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
        originalFingerprint deduplicatedFingerprint fingerprintWitness)
      nextLog)

def ay_pdch_DuplicateHashFailure
    (hashCollision : Prop) (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedDuplicateHashing : Prop) :=
  ay_pdch_Disj hashCollision
    (ay_pdch_Disj deletionMismatch
      (ay_pdch_Disj missingCoverage
        (ay_pdch_Disj representativeMismatch
          (ay_pdch_Disj brokenReconstruction
            (ay_pdch_Disj digestMismatch
              (ay_pdch_Disj replayRejected
                (ay_pdch_Disj fingerprintDrift uncheckedDuplicateHashing)))))))

def ay_pdch_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pdch_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pdch_Conj currentCnf recompute

def ay_pdch_DiagnosticDuplicateHashLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (hashCollision : Prop) (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedDuplicateHashing : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pdch_Conj previousLog
    (ay_pdch_Conj
      (ay_pdch_Conj
        (ay_pdch_DuplicateHashFailure
          hashCollision deletionMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedDuplicateHashing)
        (ay_pdch_Conj
          (ay_pdch_RecomputeObligation currentCnf recompute)
          (ay_pdch_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pdch_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pdch_Conj exitCode claim

def ay_pdch_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pdch_Disj
    (ay_pdch_ExitCodeSound exitCode (ay_pdch_Sat originalCnf model))
    (ay_pdch_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pdch_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pdch_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pdch_conj_left
    (left : Prop) (right : Prop) :
    ay_pdch_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pdch_conj_right
    (left : Prop) (right : Prop) :
    ay_pdch_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pdch_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pdch_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pdch_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pdch_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pdch_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pdch_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pdch_conj_left (before -> after) (after -> before) eq

theorem ay_pdch_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pdch_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pdch_conj_right (before -> after) (after -> before) eq

theorem ay_pdch_duplicate_clause_coverage
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pdch_AcceptedDuplicateHashReplay
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness deduplicatedModel originalModel certificate conflict
      duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
      originalFingerprint deduplicatedFingerprint fingerprintWitness ->
    ay_pdch_ClauseCoverage duplicateClauses coveredClauses coverageWitness := by
  intro accepted
  exact ay_pdch_conj_left
    (ay_pdch_ClauseCoverage duplicateClauses coveredClauses coverageWitness)
    (ay_pdch_Conj
      (ay_pdch_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_pdch_Conj
        (ay_pdch_Equisat originalCnf deduplicatedCnf)
        (ay_pdch_Conj
          (ay_pdch_ModelReconstruction
            deduplicatedCnf originalCnf deduplicatedModel originalModel)
          (ay_pdch_Conj
            (ay_pdch_ProofReconstruction
              originalCnf deduplicatedCnf certificate conflict)
            (ay_pdch_Conj
              (ay_pdch_DigestMembership duplicateHashDigest manifestDigest)
              (ay_pdch_Conj
                (ay_pdch_CheckerReplay duplicateHashCertificate checkerAccepted)
                (ay_pdch_FingerprintAgreement
                  originalFingerprint deduplicatedFingerprint
                  fingerprintWitness)))))))
    accepted

theorem ay_pdch_duplicate_representative
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pdch_AcceptedDuplicateHashReplay
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness deduplicatedModel originalModel certificate conflict
      duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
      originalFingerprint deduplicatedFingerprint fingerprintWitness ->
    ay_pdch_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness := by
  intro accepted
  exact accepted
    (ay_pdch_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_pdch_RepresentativeAgreement
          oldRepresentative newRepresentative representativeWitness)
        (fun rep _tail => rep))

theorem ay_pdch_duplicate_equisat
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pdch_AcceptedDuplicateHashReplay
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness deduplicatedModel originalModel certificate conflict
      duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
      originalFingerprint deduplicatedFingerprint fingerprintWitness ->
    ay_pdch_Equisat originalCnf deduplicatedCnf := by
  intro accepted
  exact accepted
    (ay_pdch_Equisat originalCnf deduplicatedCnf)
    (fun _coverage rest1 =>
      rest1
        (ay_pdch_Equisat originalCnf deduplicatedCnf)
        (fun _rep rest2 =>
          rest2
            (ay_pdch_Equisat originalCnf deduplicatedCnf)
            (fun eq _tail => eq)))

theorem ay_pdch_duplicate_model_reconstruction
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pdch_AcceptedDuplicateHashReplay
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness deduplicatedModel originalModel certificate conflict
      duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
      originalFingerprint deduplicatedFingerprint fingerprintWitness ->
    ay_pdch_ModelReconstruction deduplicatedCnf originalCnf deduplicatedModel
      originalModel := by
  intro accepted
  exact accepted
    (ay_pdch_ModelReconstruction
      deduplicatedCnf originalCnf deduplicatedModel originalModel)
    (fun _coverage rest1 =>
      rest1
        (ay_pdch_ModelReconstruction
          deduplicatedCnf originalCnf deduplicatedModel originalModel)
        (fun _rep rest2 =>
          rest2
            (ay_pdch_ModelReconstruction
              deduplicatedCnf originalCnf deduplicatedModel originalModel)
            (fun _eq rest3 =>
              rest3
                (ay_pdch_ModelReconstruction
                  deduplicatedCnf originalCnf deduplicatedModel originalModel)
                (fun model _tail => model))))

theorem ay_pdch_duplicate_proof_reconstruction
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pdch_AcceptedDuplicateHashReplay
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness deduplicatedModel originalModel certificate conflict
      duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
      originalFingerprint deduplicatedFingerprint fingerprintWitness ->
    ay_pdch_ProofReconstruction originalCnf deduplicatedCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_pdch_ProofReconstruction originalCnf deduplicatedCnf certificate conflict)
    (fun _coverage rest1 =>
      rest1
        (ay_pdch_ProofReconstruction originalCnf deduplicatedCnf certificate conflict)
        (fun _rep rest2 =>
          rest2
            (ay_pdch_ProofReconstruction
              originalCnf deduplicatedCnf certificate conflict)
            (fun _eq rest3 =>
              rest3
                (ay_pdch_ProofReconstruction
                  originalCnf deduplicatedCnf certificate conflict)
                (fun _model rest4 =>
                  rest4
                    (ay_pdch_ProofReconstruction
                      originalCnf deduplicatedCnf certificate conflict)
                    (fun proof _tail => proof)))))

theorem ay_pdch_duplicate_digest
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pdch_AcceptedDuplicateHashReplay
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness deduplicatedModel originalModel certificate conflict
      duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
      originalFingerprint deduplicatedFingerprint fingerprintWitness ->
    ay_pdch_DigestMembership duplicateHashDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_pdch_DigestMembership duplicateHashDigest manifestDigest)
    (fun _coverage rest1 =>
      rest1
        (ay_pdch_DigestMembership duplicateHashDigest manifestDigest)
        (fun _rep rest2 =>
          rest2
            (ay_pdch_DigestMembership duplicateHashDigest manifestDigest)
            (fun _eq rest3 =>
              rest3
                (ay_pdch_DigestMembership duplicateHashDigest manifestDigest)
                (fun _model rest4 =>
                  rest4
                    (ay_pdch_DigestMembership duplicateHashDigest manifestDigest)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pdch_DigestMembership duplicateHashDigest manifestDigest)
                        (fun digest _tail => digest))))))

theorem ay_pdch_duplicate_checker
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pdch_AcceptedDuplicateHashReplay
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness deduplicatedModel originalModel certificate conflict
      duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
      originalFingerprint deduplicatedFingerprint fingerprintWitness ->
    ay_pdch_CheckerReplay duplicateHashCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pdch_CheckerReplay duplicateHashCertificate checkerAccepted)
    (fun _coverage rest1 =>
      rest1
        (ay_pdch_CheckerReplay duplicateHashCertificate checkerAccepted)
        (fun _rep rest2 =>
          rest2
            (ay_pdch_CheckerReplay duplicateHashCertificate checkerAccepted)
            (fun _eq rest3 =>
              rest3
                (ay_pdch_CheckerReplay duplicateHashCertificate checkerAccepted)
                (fun _model rest4 =>
                  rest4
                    (ay_pdch_CheckerReplay duplicateHashCertificate checkerAccepted)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pdch_CheckerReplay
                          duplicateHashCertificate checkerAccepted)
                        (fun _digest rest6 =>
                          rest6
                            (ay_pdch_CheckerReplay
                              duplicateHashCertificate checkerAccepted)
                            (fun checker _tail => checker)))))))

theorem ay_pdch_duplicate_fingerprint
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pdch_AcceptedDuplicateHashReplay
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness deduplicatedModel originalModel certificate conflict
      duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
      originalFingerprint deduplicatedFingerprint fingerprintWitness ->
    ay_pdch_FingerprintAgreement
      originalFingerprint deduplicatedFingerprint fingerprintWitness := by
  intro accepted
  exact accepted
    (ay_pdch_FingerprintAgreement
      originalFingerprint deduplicatedFingerprint fingerprintWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_pdch_FingerprintAgreement
          originalFingerprint deduplicatedFingerprint fingerprintWitness)
        (fun _rep rest2 =>
          rest2
            (ay_pdch_FingerprintAgreement
              originalFingerprint deduplicatedFingerprint fingerprintWitness)
            (fun _eq rest3 =>
              rest3
                (ay_pdch_FingerprintAgreement
                  originalFingerprint deduplicatedFingerprint fingerprintWitness)
                (fun _model rest4 =>
                  rest4
                    (ay_pdch_FingerprintAgreement
                      originalFingerprint deduplicatedFingerprint fingerprintWitness)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pdch_FingerprintAgreement
                          originalFingerprint deduplicatedFingerprint
                          fingerprintWitness)
                        (fun _digest rest6 =>
                          rest6
                            (ay_pdch_FingerprintAgreement
                              originalFingerprint deduplicatedFingerprint
                              fingerprintWitness)
                            (fun _checker fp => fp)))))))

theorem ay_pdch_sat_pullback
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pdch_AcceptedDuplicateHashReplay
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness deduplicatedModel originalModel certificate conflict
      duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
      originalFingerprint deduplicatedFingerprint fingerprintWitness ->
    ay_pdch_Sat deduplicatedCnf deduplicatedModel ->
    ay_pdch_Sat originalCnf originalModel := by
  intro accepted deduplicatedSat
  exact
    (ay_pdch_duplicate_model_reconstruction
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative representativeWitness
      deduplicatedModel originalModel certificate conflict duplicateHashDigest
      manifestDigest duplicateHashCertificate checkerAccepted originalFingerprint
      deduplicatedFingerprint fingerprintWitness accepted)
      deduplicatedSat

theorem ay_pdch_unsat_pushback
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pdch_AcceptedDuplicateHashReplay
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness deduplicatedModel originalModel certificate conflict
      duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
      originalFingerprint deduplicatedFingerprint fingerprintWitness ->
    ay_pdch_Replay deduplicatedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay cert original
  exact
    (ay_pdch_duplicate_proof_reconstruction
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative representativeWitness
      deduplicatedModel originalModel certificate conflict duplicateHashDigest
      manifestDigest duplicateHashCertificate checkerAccepted originalFingerprint
      deduplicatedFingerprint fingerprintWitness accepted)
      replay cert original

theorem ay_pdch_public_sat
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pdch_AcceptedDuplicateHashReplay
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness deduplicatedModel originalModel certificate conflict
      duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
      originalFingerprint deduplicatedFingerprint fingerprintWitness ->
    ay_pdch_Sat deduplicatedCnf deduplicatedModel ->
    exitCode ->
    ay_pdch_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted deduplicatedSat exit
  exact ay_pdch_disj_left
    (ay_pdch_ExitCodeSound exitCode (ay_pdch_Sat originalCnf originalModel))
    (ay_pdch_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pdch_conj_intro exitCode
      (ay_pdch_Sat originalCnf originalModel)
      exit
      (ay_pdch_sat_pullback
        originalCnf deduplicatedCnf duplicateClauses coveredClauses
        coverageWitness oldRepresentative newRepresentative representativeWitness
        deduplicatedModel originalModel certificate conflict duplicateHashDigest
        manifestDigest duplicateHashCertificate checkerAccepted originalFingerprint
        deduplicatedFingerprint fingerprintWitness accepted deduplicatedSat))

theorem ay_pdch_public_unsat
    (originalCnf : Prop) (deduplicatedCnf : Prop)
    (duplicateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (deduplicatedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (duplicateHashDigest : Prop) (manifestDigest : Prop)
    (duplicateHashCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (deduplicatedFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pdch_AcceptedDuplicateHashReplay
      originalCnf deduplicatedCnf duplicateClauses coveredClauses
      coverageWitness oldRepresentative newRepresentative
      representativeWitness deduplicatedModel originalModel certificate conflict
      duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
      originalFingerprint deduplicatedFingerprint fingerprintWitness ->
    ay_pdch_Replay deduplicatedCnf certificate conflict ->
    exitCode ->
    ay_pdch_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_pdch_disj_right
    (ay_pdch_ExitCodeSound exitCode (ay_pdch_Sat originalCnf originalModel))
    (ay_pdch_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pdch_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      exit
      (fun cert original =>
        ay_pdch_unsat_pushback
          originalCnf deduplicatedCnf duplicateClauses coveredClauses
          coverageWitness oldRepresentative newRepresentative
          representativeWitness deduplicatedModel originalModel certificate conflict
          duplicateHashDigest manifestDigest duplicateHashCertificate checkerAccepted
          originalFingerprint deduplicatedFingerprint fingerprintWitness accepted
          replay cert original))

theorem ay_pdch_failure_hash_collision
    (hashCollision : Prop) (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedDuplicateHashing : Prop) :
    hashCollision ->
    ay_pdch_DuplicateHashFailure
      hashCollision deletionMismatch missingCoverage representativeMismatch
      brokenReconstruction digestMismatch replayRejected fingerprintDrift
      uncheckedDuplicateHashing := by
  intro collision
  exact ay_pdch_disj_left hashCollision
    (ay_pdch_Disj deletionMismatch
      (ay_pdch_Disj missingCoverage
        (ay_pdch_Disj representativeMismatch
          (ay_pdch_Disj brokenReconstruction
            (ay_pdch_Disj digestMismatch
              (ay_pdch_Disj replayRejected
                (ay_pdch_Disj fingerprintDrift uncheckedDuplicateHashing)))))))
    collision

theorem ay_pdch_failure_deletion_mismatch
    (hashCollision : Prop) (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedDuplicateHashing : Prop) :
    deletionMismatch ->
    ay_pdch_DuplicateHashFailure
      hashCollision deletionMismatch missingCoverage representativeMismatch
      brokenReconstruction digestMismatch replayRejected fingerprintDrift
      uncheckedDuplicateHashing := by
  intro mismatch
  exact ay_pdch_disj_right hashCollision
    (ay_pdch_Disj deletionMismatch
      (ay_pdch_Disj missingCoverage
        (ay_pdch_Disj representativeMismatch
          (ay_pdch_Disj brokenReconstruction
            (ay_pdch_Disj digestMismatch
              (ay_pdch_Disj replayRejected
                (ay_pdch_Disj fingerprintDrift uncheckedDuplicateHashing)))))))
    (ay_pdch_disj_left deletionMismatch
      (ay_pdch_Disj missingCoverage
        (ay_pdch_Disj representativeMismatch
          (ay_pdch_Disj brokenReconstruction
            (ay_pdch_Disj digestMismatch
              (ay_pdch_Disj replayRejected
                (ay_pdch_Disj fingerprintDrift uncheckedDuplicateHashing))))))
      mismatch)

theorem ay_pdch_failure_missing_coverage
    (hashCollision : Prop) (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedDuplicateHashing : Prop) :
    missingCoverage ->
    ay_pdch_DuplicateHashFailure
      hashCollision deletionMismatch missingCoverage representativeMismatch
      brokenReconstruction digestMismatch replayRejected fingerprintDrift
      uncheckedDuplicateHashing := by
  intro missing
  exact ay_pdch_disj_right hashCollision
    (ay_pdch_Disj deletionMismatch
      (ay_pdch_Disj missingCoverage
        (ay_pdch_Disj representativeMismatch
          (ay_pdch_Disj brokenReconstruction
            (ay_pdch_Disj digestMismatch
              (ay_pdch_Disj replayRejected
                (ay_pdch_Disj fingerprintDrift uncheckedDuplicateHashing)))))))
    (ay_pdch_disj_right deletionMismatch
      (ay_pdch_Disj missingCoverage
        (ay_pdch_Disj representativeMismatch
          (ay_pdch_Disj brokenReconstruction
            (ay_pdch_Disj digestMismatch
              (ay_pdch_Disj replayRejected
                (ay_pdch_Disj fingerprintDrift uncheckedDuplicateHashing))))))
      (ay_pdch_disj_left missingCoverage
        (ay_pdch_Disj representativeMismatch
          (ay_pdch_Disj brokenReconstruction
            (ay_pdch_Disj digestMismatch
              (ay_pdch_Disj replayRejected
                (ay_pdch_Disj fingerprintDrift uncheckedDuplicateHashing)))))
        missing))

theorem ay_pdch_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (hashCollision : Prop) (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedDuplicateHashing : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pdch_DiagnosticDuplicateHashLogEntry
      previousLog nextLog currentCnf hashCollision deletionMismatch
      missingCoverage representativeMismatch brokenReconstruction digestMismatch
      replayRejected fingerprintDrift uncheckedDuplicateHashing recompute
      diagnostic ->
    ay_pdch_DuplicateHashFailure
      hashCollision deletionMismatch missingCoverage representativeMismatch
      brokenReconstruction digestMismatch replayRejected fingerprintDrift
      uncheckedDuplicateHashing := by
  intro entry
  exact entry
    (ay_pdch_DuplicateHashFailure
      hashCollision deletionMismatch missingCoverage representativeMismatch
      brokenReconstruction digestMismatch replayRejected fingerprintDrift
      uncheckedDuplicateHashing)
    (fun _previous rest1 =>
      rest1
        (ay_pdch_DuplicateHashFailure
          hashCollision deletionMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedDuplicateHashing)
        (fun body _next =>
          body
            (ay_pdch_DuplicateHashFailure
              hashCollision deletionMismatch missingCoverage
              representativeMismatch brokenReconstruction digestMismatch
              replayRejected fingerprintDrift
              uncheckedDuplicateHashing)
            (fun failure _tail => failure)))

theorem ay_pdch_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (hashCollision : Prop) (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedDuplicateHashing : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pdch_DiagnosticDuplicateHashLogEntry
      previousLog nextLog currentCnf hashCollision deletionMismatch
      missingCoverage representativeMismatch brokenReconstruction digestMismatch
      replayRejected fingerprintDrift uncheckedDuplicateHashing recompute
      diagnostic ->
    ay_pdch_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_pdch_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_pdch_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_pdch_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_pdch_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_pdch_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (hashCollision : Prop) (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedDuplicateHashing : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pdch_DiagnosticDuplicateHashLogEntry
      previousLog nextLog currentCnf hashCollision deletionMismatch
      missingCoverage representativeMismatch brokenReconstruction digestMismatch
      replayRejected fingerprintDrift uncheckedDuplicateHashing recompute
      diagnostic ->
    ay_pdch_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_pdch_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_pdch_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_pdch_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_pdch_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_pdch_unchecked_duplicate_hashing_no_public_blessing
    (hashCollision : Prop) (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedDuplicateHashing : Prop)
    (diagnostic : Prop) :
    uncheckedDuplicateHashing ->
    diagnostic ->
    ay_pdch_NoSemanticClaim diagnostic := by
  intro _unchecked diag
  exact diag

theorem ay_pdch_failure_no_claim
    (hashCollision : Prop) (deletionMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedDuplicateHashing : Prop)
    (diagnostic : Prop) :
    ay_pdch_DuplicateHashFailure
      hashCollision deletionMismatch missingCoverage representativeMismatch
      brokenReconstruction digestMismatch replayRejected fingerprintDrift
      uncheckedDuplicateHashing ->
    diagnostic ->
    ay_pdch_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
