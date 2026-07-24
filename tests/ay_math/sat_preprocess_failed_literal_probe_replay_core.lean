-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Failed-literal probing replay soundness for preprocessing. The
-- propositions stand for accepted probe trace and implication coverage, representative-map
-- agreement, model/proof reconstruction, digest membership, checker replay,
-- original fingerprint agreement, diagnostics, and public SAT/UNSAT reports.

def ay_pflp_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pflp_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pflp_Equisat (before : Prop) (after : Prop) :=
  ay_pflp_Conj (before -> after) (after -> before)

def ay_pflp_Sat (cnf : Prop) (model : Prop) :=
  ay_pflp_Conj cnf model

def ay_pflp_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pflp_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pflp_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pflp_ClauseCoverage
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop) :=
  ay_pflp_Conj coverageWitness
    (implicationTrace -> coveredImplications)

def ay_pflp_RepresentativeAgreement
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop) :=
  ay_pflp_Conj representativeWitness
    (ay_pflp_IdMatch oldRepresentative newRepresentative)

def ay_pflp_ModelReconstruction
    (probeCnf : Prop) (originalCnf : Prop)
    (probeModel : Prop) (originalModel : Prop) :=
  ay_pflp_Sat probeCnf probeModel ->
    ay_pflp_Sat originalCnf originalModel

def ay_pflp_ProofReconstruction
    (originalCnf : Prop) (probeCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pflp_Replay probeCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pflp_DigestMembership
    (probeDigest : Prop) (manifestDigest : Prop) :=
  ay_pflp_Conj probeDigest manifestDigest

def ay_pflp_CheckerReplay
    (probeCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pflp_Conj probeCertificate checkerAccepted

def ay_pflp_FingerprintAgreement
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pflp_Conj fingerprintWitness
    (ay_pflp_IdMatch originalFingerprint probeFingerprint)

def ay_pflp_AcceptedProbeReplay
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pflp_Conj
    (ay_pflp_ClauseCoverage
      implicationTrace coveredImplications coverageWitness)
    (ay_pflp_Conj
      (ay_pflp_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_pflp_Conj
        (ay_pflp_Equisat originalCnf probeCnf)
        (ay_pflp_Conj
          (ay_pflp_ModelReconstruction
            probeCnf originalCnf probeModel originalModel)
          (ay_pflp_Conj
            (ay_pflp_ProofReconstruction
              originalCnf probeCnf certificate conflict)
            (ay_pflp_Conj
              (ay_pflp_DigestMembership probeDigest manifestDigest)
              (ay_pflp_Conj
                (ay_pflp_CheckerReplay
                  probeCertificate checkerAccepted)
                (ay_pflp_FingerprintAgreement
                  originalFingerprint probeFingerprint
                  fingerprintWitness)))))))

def ay_pflp_AcceptedProbeLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pflp_Conj previousLog
    (ay_pflp_Conj
      (ay_pflp_AcceptedProbeReplay
        originalCnf probeCnf implicationTrace coveredImplications
        coverageWitness oldRepresentative newRepresentative
        representativeWitness probeModel originalModel certificate conflict
        probeDigest manifestDigest probeCertificate checkerAccepted
        originalFingerprint probeFingerprint fingerprintWitness)
      nextLog)

def ay_pflp_ProbeFailure
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop) :=
  ay_pflp_Disj impliedAssignmentMismatch
    (ay_pflp_Disj missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))))

def ay_pflp_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pflp_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pflp_Conj currentCnf recompute

def ay_pflp_DiagnosticProbeLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pflp_Conj previousLog
    (ay_pflp_Conj
      (ay_pflp_Conj
        (ay_pflp_ProbeFailure
          impliedAssignmentMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedProbing)
        (ay_pflp_Conj
          (ay_pflp_RecomputeObligation currentCnf recompute)
          (ay_pflp_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pflp_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pflp_Conj exitCode claim

def ay_pflp_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pflp_Disj
    (ay_pflp_ExitCodeSound exitCode (ay_pflp_Sat originalCnf model))
    (ay_pflp_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pflp_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pflp_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pflp_conj_left
    (left : Prop) (right : Prop) :
    ay_pflp_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pflp_conj_right
    (left : Prop) (right : Prop) :
    ay_pflp_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pflp_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pflp_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pflp_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pflp_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pflp_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pflp_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pflp_conj_left (before -> after) (after -> before) eq

theorem ay_pflp_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pflp_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pflp_conj_right (before -> after) (after -> before) eq

theorem ay_pflp_probe_implication_coverage
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pflp_AcceptedProbeReplay
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness probeModel originalModel certificate conflict
      probeDigest manifestDigest probeCertificate checkerAccepted
      originalFingerprint probeFingerprint fingerprintWitness ->
    ay_pflp_ClauseCoverage implicationTrace coveredImplications coverageWitness := by
  intro accepted
  exact ay_pflp_conj_left
    (ay_pflp_ClauseCoverage implicationTrace coveredImplications coverageWitness)
    (ay_pflp_Conj
      (ay_pflp_RepresentativeAgreement
        oldRepresentative newRepresentative representativeWitness)
      (ay_pflp_Conj
        (ay_pflp_Equisat originalCnf probeCnf)
        (ay_pflp_Conj
          (ay_pflp_ModelReconstruction
            probeCnf originalCnf probeModel originalModel)
          (ay_pflp_Conj
            (ay_pflp_ProofReconstruction
              originalCnf probeCnf certificate conflict)
            (ay_pflp_Conj
              (ay_pflp_DigestMembership probeDigest manifestDigest)
              (ay_pflp_Conj
                (ay_pflp_CheckerReplay probeCertificate checkerAccepted)
                (ay_pflp_FingerprintAgreement
                  originalFingerprint probeFingerprint
                  fingerprintWitness)))))))
    accepted

theorem ay_pflp_probe_representative
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pflp_AcceptedProbeReplay
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness probeModel originalModel certificate conflict
      probeDigest manifestDigest probeCertificate checkerAccepted
      originalFingerprint probeFingerprint fingerprintWitness ->
    ay_pflp_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness := by
  intro accepted
  exact accepted
    (ay_pflp_RepresentativeAgreement
      oldRepresentative newRepresentative representativeWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_pflp_RepresentativeAgreement
          oldRepresentative newRepresentative representativeWitness)
        (fun rep _tail => rep))

theorem ay_pflp_probe_equisat
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pflp_AcceptedProbeReplay
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness probeModel originalModel certificate conflict
      probeDigest manifestDigest probeCertificate checkerAccepted
      originalFingerprint probeFingerprint fingerprintWitness ->
    ay_pflp_Equisat originalCnf probeCnf := by
  intro accepted
  exact accepted
    (ay_pflp_Equisat originalCnf probeCnf)
    (fun _coverage rest1 =>
      rest1
        (ay_pflp_Equisat originalCnf probeCnf)
        (fun _rep rest2 =>
          rest2
            (ay_pflp_Equisat originalCnf probeCnf)
            (fun eq _tail => eq)))

theorem ay_pflp_probe_model_reconstruction
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pflp_AcceptedProbeReplay
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness probeModel originalModel certificate conflict
      probeDigest manifestDigest probeCertificate checkerAccepted
      originalFingerprint probeFingerprint fingerprintWitness ->
    ay_pflp_ModelReconstruction probeCnf originalCnf probeModel
      originalModel := by
  intro accepted
  exact accepted
    (ay_pflp_ModelReconstruction
      probeCnf originalCnf probeModel originalModel)
    (fun _coverage rest1 =>
      rest1
        (ay_pflp_ModelReconstruction
          probeCnf originalCnf probeModel originalModel)
        (fun _rep rest2 =>
          rest2
            (ay_pflp_ModelReconstruction
              probeCnf originalCnf probeModel originalModel)
            (fun _eq rest3 =>
              rest3
                (ay_pflp_ModelReconstruction
                  probeCnf originalCnf probeModel originalModel)
                (fun model _tail => model))))

theorem ay_pflp_probe_proof_reconstruction
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pflp_AcceptedProbeReplay
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness probeModel originalModel certificate conflict
      probeDigest manifestDigest probeCertificate checkerAccepted
      originalFingerprint probeFingerprint fingerprintWitness ->
    ay_pflp_ProofReconstruction originalCnf probeCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_pflp_ProofReconstruction originalCnf probeCnf certificate conflict)
    (fun _coverage rest1 =>
      rest1
        (ay_pflp_ProofReconstruction originalCnf probeCnf certificate conflict)
        (fun _rep rest2 =>
          rest2
            (ay_pflp_ProofReconstruction
              originalCnf probeCnf certificate conflict)
            (fun _eq rest3 =>
              rest3
                (ay_pflp_ProofReconstruction
                  originalCnf probeCnf certificate conflict)
                (fun _model rest4 =>
                  rest4
                    (ay_pflp_ProofReconstruction
                      originalCnf probeCnf certificate conflict)
                    (fun proof _tail => proof)))))

theorem ay_pflp_probe_digest
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pflp_AcceptedProbeReplay
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness probeModel originalModel certificate conflict
      probeDigest manifestDigest probeCertificate checkerAccepted
      originalFingerprint probeFingerprint fingerprintWitness ->
    ay_pflp_DigestMembership probeDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_pflp_DigestMembership probeDigest manifestDigest)
    (fun _coverage rest1 =>
      rest1
        (ay_pflp_DigestMembership probeDigest manifestDigest)
        (fun _rep rest2 =>
          rest2
            (ay_pflp_DigestMembership probeDigest manifestDigest)
            (fun _eq rest3 =>
              rest3
                (ay_pflp_DigestMembership probeDigest manifestDigest)
                (fun _model rest4 =>
                  rest4
                    (ay_pflp_DigestMembership probeDigest manifestDigest)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pflp_DigestMembership probeDigest manifestDigest)
                        (fun digest _tail => digest))))))

theorem ay_pflp_probe_checker
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pflp_AcceptedProbeReplay
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness probeModel originalModel certificate conflict
      probeDigest manifestDigest probeCertificate checkerAccepted
      originalFingerprint probeFingerprint fingerprintWitness ->
    ay_pflp_CheckerReplay probeCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pflp_CheckerReplay probeCertificate checkerAccepted)
    (fun _coverage rest1 =>
      rest1
        (ay_pflp_CheckerReplay probeCertificate checkerAccepted)
        (fun _rep rest2 =>
          rest2
            (ay_pflp_CheckerReplay probeCertificate checkerAccepted)
            (fun _eq rest3 =>
              rest3
                (ay_pflp_CheckerReplay probeCertificate checkerAccepted)
                (fun _model rest4 =>
                  rest4
                    (ay_pflp_CheckerReplay probeCertificate checkerAccepted)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pflp_CheckerReplay
                          probeCertificate checkerAccepted)
                        (fun _digest rest6 =>
                          rest6
                            (ay_pflp_CheckerReplay
                              probeCertificate checkerAccepted)
                            (fun checker _tail => checker)))))))

theorem ay_pflp_probe_fingerprint
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pflp_AcceptedProbeReplay
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness probeModel originalModel certificate conflict
      probeDigest manifestDigest probeCertificate checkerAccepted
      originalFingerprint probeFingerprint fingerprintWitness ->
    ay_pflp_FingerprintAgreement
      originalFingerprint probeFingerprint fingerprintWitness := by
  intro accepted
  exact accepted
    (ay_pflp_FingerprintAgreement
      originalFingerprint probeFingerprint fingerprintWitness)
    (fun _coverage rest1 =>
      rest1
        (ay_pflp_FingerprintAgreement
          originalFingerprint probeFingerprint fingerprintWitness)
        (fun _rep rest2 =>
          rest2
            (ay_pflp_FingerprintAgreement
              originalFingerprint probeFingerprint fingerprintWitness)
            (fun _eq rest3 =>
              rest3
                (ay_pflp_FingerprintAgreement
                  originalFingerprint probeFingerprint fingerprintWitness)
                (fun _model rest4 =>
                  rest4
                    (ay_pflp_FingerprintAgreement
                      originalFingerprint probeFingerprint fingerprintWitness)
                    (fun _proof rest5 =>
                      rest5
                        (ay_pflp_FingerprintAgreement
                          originalFingerprint probeFingerprint
                          fingerprintWitness)
                        (fun _digest rest6 =>
                          rest6
                            (ay_pflp_FingerprintAgreement
                              originalFingerprint probeFingerprint
                              fingerprintWitness)
                            (fun _checker fp => fp)))))))

theorem ay_pflp_sat_pullback
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pflp_AcceptedProbeReplay
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness probeModel originalModel certificate conflict
      probeDigest manifestDigest probeCertificate checkerAccepted
      originalFingerprint probeFingerprint fingerprintWitness ->
    ay_pflp_Sat probeCnf probeModel ->
    ay_pflp_Sat originalCnf originalModel := by
  intro accepted probeSat
  exact
    (ay_pflp_probe_model_reconstruction
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative representativeWitness
      probeModel originalModel certificate conflict probeDigest
      manifestDigest probeCertificate checkerAccepted originalFingerprint
      probeFingerprint fingerprintWitness accepted)
      probeSat

theorem ay_pflp_unsat_pushback
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pflp_AcceptedProbeReplay
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness probeModel originalModel certificate conflict
      probeDigest manifestDigest probeCertificate checkerAccepted
      originalFingerprint probeFingerprint fingerprintWitness ->
    ay_pflp_Replay probeCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay cert original
  exact
    (ay_pflp_probe_proof_reconstruction
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative representativeWitness
      probeModel originalModel certificate conflict probeDigest
      manifestDigest probeCertificate checkerAccepted originalFingerprint
      probeFingerprint fingerprintWitness accepted)
      replay cert original

theorem ay_pflp_public_sat
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pflp_AcceptedProbeReplay
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness probeModel originalModel certificate conflict
      probeDigest manifestDigest probeCertificate checkerAccepted
      originalFingerprint probeFingerprint fingerprintWitness ->
    ay_pflp_Sat probeCnf probeModel ->
    exitCode ->
    ay_pflp_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted probeSat exit
  exact ay_pflp_disj_left
    (ay_pflp_ExitCodeSound exitCode (ay_pflp_Sat originalCnf originalModel))
    (ay_pflp_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pflp_conj_intro exitCode
      (ay_pflp_Sat originalCnf originalModel)
      exit
      (ay_pflp_sat_pullback
        originalCnf probeCnf implicationTrace coveredImplications
        coverageWitness oldRepresentative newRepresentative representativeWitness
        probeModel originalModel certificate conflict probeDigest
        manifestDigest probeCertificate checkerAccepted originalFingerprint
        probeFingerprint fingerprintWitness accepted probeSat))

theorem ay_pflp_public_unsat
    (originalCnf : Prop) (probeCnf : Prop)
    (implicationTrace : Prop) (coveredImplications : Prop)
    (coverageWitness : Prop)
    (oldRepresentative : Prop) (newRepresentative : Prop)
    (representativeWitness : Prop)
    (probeModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (probeDigest : Prop) (manifestDigest : Prop)
    (probeCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (probeFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pflp_AcceptedProbeReplay
      originalCnf probeCnf implicationTrace coveredImplications
      coverageWitness oldRepresentative newRepresentative
      representativeWitness probeModel originalModel certificate conflict
      probeDigest manifestDigest probeCertificate checkerAccepted
      originalFingerprint probeFingerprint fingerprintWitness ->
    ay_pflp_Replay probeCnf certificate conflict ->
    exitCode ->
    ay_pflp_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_pflp_disj_right
    (ay_pflp_ExitCodeSound exitCode (ay_pflp_Sat originalCnf originalModel))
    (ay_pflp_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pflp_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      exit
      (fun cert original =>
        ay_pflp_unsat_pushback
          originalCnf probeCnf implicationTrace coveredImplications
          coverageWitness oldRepresentative newRepresentative
          representativeWitness probeModel originalModel certificate conflict
          probeDigest manifestDigest probeCertificate checkerAccepted
          originalFingerprint probeFingerprint fingerprintWitness accepted
          replay cert original))

theorem ay_pflp_failure_implied_assignment_mismatch
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop) :
    impliedAssignmentMismatch ->
    ay_pflp_ProbeFailure
      impliedAssignmentMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedProbing := by
  intro mismatch
  exact ay_pflp_disj_left impliedAssignmentMismatch
    (ay_pflp_Disj missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))))
    mismatch

theorem ay_pflp_failure_missing_coverage
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop) :
    missingCoverage ->
    ay_pflp_ProbeFailure
      impliedAssignmentMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedProbing := by
  intro missing
  exact ay_pflp_disj_right impliedAssignmentMismatch
    (ay_pflp_Disj missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))))
    (ay_pflp_disj_left missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)))))
      missing)

theorem ay_pflp_failure_representative_mismatch
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop) :
    representativeMismatch ->
    ay_pflp_ProbeFailure
      impliedAssignmentMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedProbing := by
  intro mismatch
  exact ay_pflp_disj_right impliedAssignmentMismatch
    (ay_pflp_Disj missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))))
    (ay_pflp_disj_right missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)))))
      (ay_pflp_disj_left representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))
        mismatch))

theorem ay_pflp_failure_broken_reconstruction
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop) :
    brokenReconstruction ->
    ay_pflp_ProbeFailure
      impliedAssignmentMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedProbing := by
  intro broken
  exact ay_pflp_disj_right impliedAssignmentMismatch
    (ay_pflp_Disj missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))))
    (ay_pflp_disj_right missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)))))
      (ay_pflp_disj_right representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))
        (ay_pflp_disj_left brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)))
          broken)))

theorem ay_pflp_failure_digest_mismatch
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop) :
    digestMismatch ->
    ay_pflp_ProbeFailure
      impliedAssignmentMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedProbing := by
  intro mismatch
  exact ay_pflp_disj_right impliedAssignmentMismatch
    (ay_pflp_Disj missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))))
    (ay_pflp_disj_right missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)))))
      (ay_pflp_disj_right representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))
        (ay_pflp_disj_right brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)))
          (ay_pflp_disj_left digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))
            mismatch))))

theorem ay_pflp_failure_replay_rejected
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop) :
    replayRejected ->
    ay_pflp_ProbeFailure
      impliedAssignmentMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedProbing := by
  intro rejected
  exact ay_pflp_disj_right impliedAssignmentMismatch
    (ay_pflp_Disj missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))))
    (ay_pflp_disj_right missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)))))
      (ay_pflp_disj_right representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))
        (ay_pflp_disj_right brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)))
          (ay_pflp_disj_right digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))
            (ay_pflp_disj_left replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)
              rejected)))))

theorem ay_pflp_failure_fingerprint_drift
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop) :
    fingerprintDrift ->
    ay_pflp_ProbeFailure
      impliedAssignmentMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedProbing := by
  intro drift
  exact ay_pflp_disj_right impliedAssignmentMismatch
    (ay_pflp_Disj missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))))
    (ay_pflp_disj_right missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)))))
      (ay_pflp_disj_right representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))
        (ay_pflp_disj_right brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)))
          (ay_pflp_disj_right digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))
            (ay_pflp_disj_right replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)
              (ay_pflp_disj_left fingerprintDrift uncheckedProbing drift))))))

theorem ay_pflp_failure_unchecked_probing
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop) :
    uncheckedProbing ->
    ay_pflp_ProbeFailure
      impliedAssignmentMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedProbing := by
  intro unchecked
  exact ay_pflp_disj_right impliedAssignmentMismatch
    (ay_pflp_Disj missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))))
    (ay_pflp_disj_right missingCoverage
      (ay_pflp_Disj representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)))))
      (ay_pflp_disj_right representativeMismatch
        (ay_pflp_Disj brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))))
        (ay_pflp_disj_right brokenReconstruction
          (ay_pflp_Disj digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)))
          (ay_pflp_disj_right digestMismatch
            (ay_pflp_Disj replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing))
            (ay_pflp_disj_right replayRejected
              (ay_pflp_Disj fingerprintDrift uncheckedProbing)
              (ay_pflp_disj_right fingerprintDrift uncheckedProbing
                unchecked))))))

theorem ay_pflp_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pflp_DiagnosticProbeLogEntry
      previousLog nextLog currentCnf impliedAssignmentMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedProbing recompute diagnostic ->
    ay_pflp_ProbeFailure
      impliedAssignmentMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedProbing := by
  intro entry
  exact entry
    (ay_pflp_ProbeFailure
      impliedAssignmentMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedProbing)
    (fun _previous rest1 =>
      rest1
        (ay_pflp_ProbeFailure
          impliedAssignmentMismatch missingCoverage representativeMismatch
          brokenReconstruction digestMismatch replayRejected fingerprintDrift
          uncheckedProbing)
        (fun body _next =>
          body
            (ay_pflp_ProbeFailure
              impliedAssignmentMismatch missingCoverage representativeMismatch
              brokenReconstruction digestMismatch replayRejected fingerprintDrift
              uncheckedProbing)
            (fun failure _tail => failure)))

theorem ay_pflp_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pflp_DiagnosticProbeLogEntry
      previousLog nextLog currentCnf impliedAssignmentMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedProbing recompute diagnostic ->
    ay_pflp_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_pflp_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_pflp_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_pflp_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_pflp_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_pflp_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pflp_DiagnosticProbeLogEntry
      previousLog nextLog currentCnf impliedAssignmentMismatch missingCoverage
      representativeMismatch brokenReconstruction digestMismatch replayRejected
      fingerprintDrift uncheckedProbing recompute diagnostic ->
    ay_pflp_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_pflp_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_pflp_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_pflp_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_pflp_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_pflp_unchecked_probing_no_public_blessing
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop)
    (diagnostic : Prop) :
    uncheckedProbing ->
    diagnostic ->
    ay_pflp_NoSemanticClaim diagnostic := by
  intro _unchecked diag
  exact diag

theorem ay_pflp_failure_no_claim
    (impliedAssignmentMismatch : Prop) (missingCoverage : Prop)
    (representativeMismatch : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (uncheckedProbing : Prop)
    (diagnostic : Prop) :
    ay_pflp_ProbeFailure
      impliedAssignmentMismatch missingCoverage representativeMismatch brokenReconstruction
      digestMismatch replayRejected fingerprintDrift uncheckedProbing ->
    diagnostic ->
    ay_pflp_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
