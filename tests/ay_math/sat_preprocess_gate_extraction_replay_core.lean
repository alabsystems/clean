-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Gate-extraction replay soundness for preprocessing. The propositions stand
-- for gate/XOR/AND-OR detection evidence, representative variable maps,
-- clause coverage, model/proof reconstruction hooks, digest membership,
-- checker replay, original-instance fingerprint agreement, diagnostics, and
-- public SAT/UNSAT reports.

def ay_pger_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pger_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pger_Equisat (before : Prop) (after : Prop) :=
  ay_pger_Conj (before -> after) (after -> before)

def ay_pger_Sat (cnf : Prop) (model : Prop) :=
  ay_pger_Conj cnf model

def ay_pger_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_pger_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_pger_Conj (leftId -> rightId) (rightId -> leftId)

def ay_pger_GateDetectionEvidence
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop) :=
  ay_pger_Conj detectionWitness
    (ay_pger_Conj detectedGate encodingClauses)

def ay_pger_RepresentativeVariableMap
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop) :=
  ay_pger_Conj representativeWitness
    (gateOutput -> representativeVariable)

def ay_pger_ClauseCoverage
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop) :=
  ay_pger_Conj coverageWitness
    (gateClauses -> coveredClauses)

def ay_pger_ModelReconstruction
    (rewrittenCnf : Prop) (originalCnf : Prop)
    (rewrittenModel : Prop) (originalModel : Prop) :=
  ay_pger_Sat rewrittenCnf rewrittenModel ->
    ay_pger_Sat originalCnf originalModel

def ay_pger_ProofReconstruction
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_pger_Replay rewrittenCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_pger_DigestMembership
    (gateDigest : Prop) (manifestDigest : Prop) :=
  ay_pger_Conj gateDigest manifestDigest

def ay_pger_CheckerReplay
    (gateCertificate : Prop) (checkerAccepted : Prop) :=
  ay_pger_Conj gateCertificate checkerAccepted

def ay_pger_FingerprintAgreement
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pger_Conj fingerprintWitness
    (ay_pger_IdMatch originalFingerprint rewrittenFingerprint)

def ay_pger_AcceptedGateExtraction
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pger_Conj
    (ay_pger_GateDetectionEvidence
      detectedGate encodingClauses detectionWitness)
    (ay_pger_Conj
      (ay_pger_RepresentativeVariableMap
        gateOutput representativeVariable representativeWitness)
      (ay_pger_Conj
        (ay_pger_ClauseCoverage gateClauses coveredClauses coverageWitness)
        (ay_pger_Conj
          (ay_pger_Equisat originalCnf rewrittenCnf)
          (ay_pger_Conj
            (ay_pger_ModelReconstruction
              rewrittenCnf originalCnf rewrittenModel originalModel)
            (ay_pger_Conj
              (ay_pger_ProofReconstruction
                originalCnf rewrittenCnf certificate conflict)
              (ay_pger_Conj
                (ay_pger_DigestMembership gateDigest manifestDigest)
                (ay_pger_Conj
                  (ay_pger_CheckerReplay gateCertificate checkerAccepted)
                  (ay_pger_FingerprintAgreement
                    originalFingerprint rewrittenFingerprint
                    fingerprintWitness))))))))

def ay_pger_AcceptedGateLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :=
  ay_pger_Conj previousLog
    (ay_pger_Conj
      (ay_pger_AcceptedGateExtraction
        originalCnf rewrittenCnf detectedGate encodingClauses
        detectionWitness gateOutput representativeVariable
        representativeWitness gateClauses coveredClauses coverageWitness
        rewrittenModel originalModel certificate conflict gateDigest
        manifestDigest gateCertificate checkerAccepted originalFingerprint
        rewrittenFingerprint fingerprintWitness)
      nextLog)

def ay_pger_GateFailure
    (falseGateDetection : Prop) (missingRepresentative : Prop)
    (clauseCoverageGap : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :=
  ay_pger_Disj falseGateDetection
    (ay_pger_Disj missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)))))

def ay_pger_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_pger_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_pger_Conj currentCnf recompute

def ay_pger_DiagnosticGateLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (falseGateDetection : Prop) (missingRepresentative : Prop)
    (clauseCoverageGap : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_pger_Conj previousLog
    (ay_pger_Conj
      (ay_pger_Conj
        (ay_pger_GateFailure
          falseGateDetection missingRepresentative clauseCoverageGap
          brokenReconstruction digestMismatch replayRejected fingerprintDrift)
        (ay_pger_Conj
          (ay_pger_RecomputeObligation currentCnf recompute)
          (ay_pger_NoSemanticClaim diagnostic)))
      nextLog)

def ay_pger_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_pger_Conj exitCode claim

def ay_pger_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_pger_Disj
    (ay_pger_ExitCodeSound exitCode (ay_pger_Sat originalCnf model))
    (ay_pger_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_pger_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_pger_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_pger_conj_left
    (left : Prop) (right : Prop) :
    ay_pger_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_pger_conj_right
    (left : Prop) (right : Prop) :
    ay_pger_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_pger_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_pger_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_pger_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_pger_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_pger_equisat_forward
    (before : Prop) (after : Prop) :
    ay_pger_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_pger_conj_left (before -> after) (after -> before) eq

theorem ay_pger_equisat_backward
    (before : Prop) (after : Prop) :
    ay_pger_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_pger_conj_right (before -> after) (after -> before) eq

theorem ay_pger_gate_detection
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pger_AcceptedGateExtraction
      originalCnf rewrittenCnf detectedGate encodingClauses
      detectionWitness gateOutput representativeVariable representativeWitness
      gateClauses coveredClauses coverageWitness rewrittenModel originalModel
      certificate conflict gateDigest manifestDigest gateCertificate
      checkerAccepted originalFingerprint rewrittenFingerprint
      fingerprintWitness ->
    ay_pger_GateDetectionEvidence
      detectedGate encodingClauses detectionWitness := by
  intro accepted
  exact ay_pger_conj_left
    (ay_pger_GateDetectionEvidence
      detectedGate encodingClauses detectionWitness)
    (ay_pger_Conj
      (ay_pger_RepresentativeVariableMap
        gateOutput representativeVariable representativeWitness)
      (ay_pger_Conj
        (ay_pger_ClauseCoverage gateClauses coveredClauses coverageWitness)
        (ay_pger_Conj
          (ay_pger_Equisat originalCnf rewrittenCnf)
          (ay_pger_Conj
            (ay_pger_ModelReconstruction
              rewrittenCnf originalCnf rewrittenModel originalModel)
            (ay_pger_Conj
              (ay_pger_ProofReconstruction
                originalCnf rewrittenCnf certificate conflict)
              (ay_pger_Conj
                (ay_pger_DigestMembership gateDigest manifestDigest)
                (ay_pger_Conj
                  (ay_pger_CheckerReplay gateCertificate checkerAccepted)
                  (ay_pger_FingerprintAgreement
                    originalFingerprint rewrittenFingerprint
                    fingerprintWitness))))))))
    accepted

theorem ay_pger_representative_map
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pger_AcceptedGateExtraction
      originalCnf rewrittenCnf detectedGate encodingClauses
      detectionWitness gateOutput representativeVariable representativeWitness
      gateClauses coveredClauses coverageWitness rewrittenModel originalModel
      certificate conflict gateDigest manifestDigest gateCertificate
      checkerAccepted originalFingerprint rewrittenFingerprint
      fingerprintWitness ->
    ay_pger_RepresentativeVariableMap
      gateOutput representativeVariable representativeWitness := by
  intro accepted
  exact accepted
    (ay_pger_RepresentativeVariableMap
      gateOutput representativeVariable representativeWitness)
    (fun _gate rest1 =>
      rest1
        (ay_pger_RepresentativeVariableMap
          gateOutput representativeVariable representativeWitness)
        (fun rep _tail => rep))

theorem ay_pger_clause_coverage
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pger_AcceptedGateExtraction
      originalCnf rewrittenCnf detectedGate encodingClauses
      detectionWitness gateOutput representativeVariable representativeWitness
      gateClauses coveredClauses coverageWitness rewrittenModel originalModel
      certificate conflict gateDigest manifestDigest gateCertificate
      checkerAccepted originalFingerprint rewrittenFingerprint
      fingerprintWitness ->
    ay_pger_ClauseCoverage gateClauses coveredClauses coverageWitness := by
  intro accepted
  exact accepted
    (ay_pger_ClauseCoverage gateClauses coveredClauses coverageWitness)
    (fun _gate rest1 =>
      rest1
        (ay_pger_ClauseCoverage gateClauses coveredClauses coverageWitness)
        (fun _rep rest2 =>
          rest2
            (ay_pger_ClauseCoverage gateClauses coveredClauses coverageWitness)
            (fun coverage _tail => coverage)))

theorem ay_pger_gate_equisat
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pger_AcceptedGateExtraction
      originalCnf rewrittenCnf detectedGate encodingClauses
      detectionWitness gateOutput representativeVariable representativeWitness
      gateClauses coveredClauses coverageWitness rewrittenModel originalModel
      certificate conflict gateDigest manifestDigest gateCertificate
      checkerAccepted originalFingerprint rewrittenFingerprint
      fingerprintWitness ->
    ay_pger_Equisat originalCnf rewrittenCnf := by
  intro accepted
  exact accepted
    (ay_pger_Equisat originalCnf rewrittenCnf)
    (fun _gate rest1 =>
      rest1
        (ay_pger_Equisat originalCnf rewrittenCnf)
        (fun _rep rest2 =>
          rest2
            (ay_pger_Equisat originalCnf rewrittenCnf)
            (fun _coverage rest3 =>
              rest3
                (ay_pger_Equisat originalCnf rewrittenCnf)
                (fun eq _tail => eq))))

theorem ay_pger_model_reconstruction
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pger_AcceptedGateExtraction
      originalCnf rewrittenCnf detectedGate encodingClauses
      detectionWitness gateOutput representativeVariable representativeWitness
      gateClauses coveredClauses coverageWitness rewrittenModel originalModel
      certificate conflict gateDigest manifestDigest gateCertificate
      checkerAccepted originalFingerprint rewrittenFingerprint
      fingerprintWitness ->
    ay_pger_ModelReconstruction rewrittenCnf originalCnf rewrittenModel
      originalModel := by
  intro accepted
  exact accepted
    (ay_pger_ModelReconstruction
      rewrittenCnf originalCnf rewrittenModel originalModel)
    (fun _gate rest1 =>
      rest1
        (ay_pger_ModelReconstruction
          rewrittenCnf originalCnf rewrittenModel originalModel)
        (fun _rep rest2 =>
          rest2
            (ay_pger_ModelReconstruction
              rewrittenCnf originalCnf rewrittenModel originalModel)
            (fun _coverage rest3 =>
              rest3
                (ay_pger_ModelReconstruction
                  rewrittenCnf originalCnf rewrittenModel originalModel)
                (fun _eq rest4 =>
                  rest4
                    (ay_pger_ModelReconstruction
                      rewrittenCnf originalCnf rewrittenModel originalModel)
                    (fun model _tail => model)))))

theorem ay_pger_proof_reconstruction
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pger_AcceptedGateExtraction
      originalCnf rewrittenCnf detectedGate encodingClauses
      detectionWitness gateOutput representativeVariable representativeWitness
      gateClauses coveredClauses coverageWitness rewrittenModel originalModel
      certificate conflict gateDigest manifestDigest gateCertificate
      checkerAccepted originalFingerprint rewrittenFingerprint
      fingerprintWitness ->
    ay_pger_ProofReconstruction originalCnf rewrittenCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_pger_ProofReconstruction originalCnf rewrittenCnf certificate conflict)
    (fun _gate rest1 =>
      rest1
        (ay_pger_ProofReconstruction originalCnf rewrittenCnf certificate conflict)
        (fun _rep rest2 =>
          rest2
            (ay_pger_ProofReconstruction
              originalCnf rewrittenCnf certificate conflict)
            (fun _coverage rest3 =>
              rest3
                (ay_pger_ProofReconstruction
                  originalCnf rewrittenCnf certificate conflict)
                (fun _eq rest4 =>
                  rest4
                    (ay_pger_ProofReconstruction
                      originalCnf rewrittenCnf certificate conflict)
                    (fun _model rest5 =>
                      rest5
                        (ay_pger_ProofReconstruction
                          originalCnf rewrittenCnf certificate conflict)
                        (fun proof _tail => proof))))))

theorem ay_pger_digest
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pger_AcceptedGateExtraction
      originalCnf rewrittenCnf detectedGate encodingClauses
      detectionWitness gateOutput representativeVariable representativeWitness
      gateClauses coveredClauses coverageWitness rewrittenModel originalModel
      certificate conflict gateDigest manifestDigest gateCertificate
      checkerAccepted originalFingerprint rewrittenFingerprint
      fingerprintWitness ->
    ay_pger_DigestMembership gateDigest manifestDigest := by
  intro accepted
  exact accepted
    (ay_pger_DigestMembership gateDigest manifestDigest)
    (fun _gate rest1 =>
      rest1
        (ay_pger_DigestMembership gateDigest manifestDigest)
        (fun _rep rest2 =>
          rest2
            (ay_pger_DigestMembership gateDigest manifestDigest)
            (fun _coverage rest3 =>
              rest3
                (ay_pger_DigestMembership gateDigest manifestDigest)
                (fun _eq rest4 =>
                  rest4
                    (ay_pger_DigestMembership gateDigest manifestDigest)
                    (fun _model rest5 =>
                      rest5
                        (ay_pger_DigestMembership gateDigest manifestDigest)
                        (fun _proof rest6 =>
                          rest6
                            (ay_pger_DigestMembership gateDigest manifestDigest)
                            (fun digest _tail => digest)))))))

theorem ay_pger_checker
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pger_AcceptedGateExtraction
      originalCnf rewrittenCnf detectedGate encodingClauses
      detectionWitness gateOutput representativeVariable representativeWitness
      gateClauses coveredClauses coverageWitness rewrittenModel originalModel
      certificate conflict gateDigest manifestDigest gateCertificate
      checkerAccepted originalFingerprint rewrittenFingerprint
      fingerprintWitness ->
    ay_pger_CheckerReplay gateCertificate checkerAccepted := by
  intro accepted
  exact accepted
    (ay_pger_CheckerReplay gateCertificate checkerAccepted)
    (fun _gate rest1 =>
      rest1
        (ay_pger_CheckerReplay gateCertificate checkerAccepted)
        (fun _rep rest2 =>
          rest2
            (ay_pger_CheckerReplay gateCertificate checkerAccepted)
            (fun _coverage rest3 =>
              rest3
                (ay_pger_CheckerReplay gateCertificate checkerAccepted)
                (fun _eq rest4 =>
                  rest4
                    (ay_pger_CheckerReplay gateCertificate checkerAccepted)
                    (fun _model rest5 =>
                      rest5
                        (ay_pger_CheckerReplay gateCertificate checkerAccepted)
                        (fun _proof rest6 =>
                          rest6
                            (ay_pger_CheckerReplay
                              gateCertificate checkerAccepted)
                            (fun _digest rest7 =>
                              rest7
                                (ay_pger_CheckerReplay
                                  gateCertificate checkerAccepted)
                                (fun checker _tail => checker))))))))

theorem ay_pger_fingerprint
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pger_AcceptedGateExtraction
      originalCnf rewrittenCnf detectedGate encodingClauses
      detectionWitness gateOutput representativeVariable representativeWitness
      gateClauses coveredClauses coverageWitness rewrittenModel originalModel
      certificate conflict gateDigest manifestDigest gateCertificate
      checkerAccepted originalFingerprint rewrittenFingerprint
      fingerprintWitness ->
    ay_pger_FingerprintAgreement
      originalFingerprint rewrittenFingerprint fingerprintWitness := by
  intro accepted
  exact accepted
    (ay_pger_FingerprintAgreement
      originalFingerprint rewrittenFingerprint fingerprintWitness)
    (fun _gate rest1 =>
      rest1
        (ay_pger_FingerprintAgreement
          originalFingerprint rewrittenFingerprint fingerprintWitness)
        (fun _rep rest2 =>
          rest2
            (ay_pger_FingerprintAgreement
              originalFingerprint rewrittenFingerprint fingerprintWitness)
            (fun _coverage rest3 =>
              rest3
                (ay_pger_FingerprintAgreement
                  originalFingerprint rewrittenFingerprint fingerprintWitness)
                (fun _eq rest4 =>
                  rest4
                    (ay_pger_FingerprintAgreement
                      originalFingerprint rewrittenFingerprint fingerprintWitness)
                    (fun _model rest5 =>
                      rest5
                        (ay_pger_FingerprintAgreement
                          originalFingerprint rewrittenFingerprint
                          fingerprintWitness)
                        (fun _proof rest6 =>
                          rest6
                            (ay_pger_FingerprintAgreement
                              originalFingerprint rewrittenFingerprint
                              fingerprintWitness)
                            (fun _digest rest7 =>
                              rest7
                                (ay_pger_FingerprintAgreement
                                  originalFingerprint rewrittenFingerprint
                                  fingerprintWitness)
                                (fun _checker fp => fp))))))))

theorem ay_pger_sat_pullback
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pger_AcceptedGateExtraction
      originalCnf rewrittenCnf detectedGate encodingClauses
      detectionWitness gateOutput representativeVariable representativeWitness
      gateClauses coveredClauses coverageWitness rewrittenModel originalModel
      certificate conflict gateDigest manifestDigest gateCertificate
      checkerAccepted originalFingerprint rewrittenFingerprint
      fingerprintWitness ->
    ay_pger_Sat rewrittenCnf rewrittenModel ->
    ay_pger_Sat originalCnf originalModel := by
  intro accepted rewrittenSat
  exact
    (ay_pger_model_reconstruction
      originalCnf rewrittenCnf detectedGate encodingClauses detectionWitness
      gateOutput representativeVariable representativeWitness gateClauses
      coveredClauses coverageWitness rewrittenModel originalModel certificate
      conflict gateDigest manifestDigest gateCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness accepted)
      rewrittenSat

theorem ay_pger_unsat_pushback
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop) :
    ay_pger_AcceptedGateExtraction
      originalCnf rewrittenCnf detectedGate encodingClauses
      detectionWitness gateOutput representativeVariable representativeWitness
      gateClauses coveredClauses coverageWitness rewrittenModel originalModel
      certificate conflict gateDigest manifestDigest gateCertificate
      checkerAccepted originalFingerprint rewrittenFingerprint
      fingerprintWitness ->
    ay_pger_Replay rewrittenCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay cert original
  exact
    (ay_pger_proof_reconstruction
      originalCnf rewrittenCnf detectedGate encodingClauses detectionWitness
      gateOutput representativeVariable representativeWitness gateClauses
      coveredClauses coverageWitness rewrittenModel originalModel certificate
      conflict gateDigest manifestDigest gateCertificate checkerAccepted
      originalFingerprint rewrittenFingerprint fingerprintWitness accepted)
      replay cert original

theorem ay_pger_public_sat
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pger_AcceptedGateExtraction
      originalCnf rewrittenCnf detectedGate encodingClauses
      detectionWitness gateOutput representativeVariable representativeWitness
      gateClauses coveredClauses coverageWitness rewrittenModel originalModel
      certificate conflict gateDigest manifestDigest gateCertificate
      checkerAccepted originalFingerprint rewrittenFingerprint
      fingerprintWitness ->
    ay_pger_Sat rewrittenCnf rewrittenModel ->
    exitCode ->
    ay_pger_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted rewrittenSat exit
  exact ay_pger_disj_left
    (ay_pger_ExitCodeSound exitCode (ay_pger_Sat originalCnf originalModel))
    (ay_pger_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pger_conj_intro exitCode
      (ay_pger_Sat originalCnf originalModel)
      exit
      (ay_pger_sat_pullback
        originalCnf rewrittenCnf detectedGate encodingClauses detectionWitness
        gateOutput representativeVariable representativeWitness gateClauses
        coveredClauses coverageWitness rewrittenModel originalModel certificate
        conflict gateDigest manifestDigest gateCertificate checkerAccepted
        originalFingerprint rewrittenFingerprint fingerprintWitness accepted
        rewrittenSat))

theorem ay_pger_public_unsat
    (originalCnf : Prop) (rewrittenCnf : Prop)
    (detectedGate : Prop) (encodingClauses : Prop)
    (detectionWitness : Prop)
    (gateOutput : Prop) (representativeVariable : Prop)
    (representativeWitness : Prop)
    (gateClauses : Prop) (coveredClauses : Prop)
    (coverageWitness : Prop)
    (rewrittenModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (gateDigest : Prop) (manifestDigest : Prop)
    (gateCertificate : Prop) (checkerAccepted : Prop)
    (originalFingerprint : Prop) (rewrittenFingerprint : Prop)
    (fingerprintWitness : Prop)
    (exitCode : Prop) :
    ay_pger_AcceptedGateExtraction
      originalCnf rewrittenCnf detectedGate encodingClauses
      detectionWitness gateOutput representativeVariable representativeWitness
      gateClauses coveredClauses coverageWitness rewrittenModel originalModel
      certificate conflict gateDigest manifestDigest gateCertificate
      checkerAccepted originalFingerprint rewrittenFingerprint
      fingerprintWitness ->
    ay_pger_Replay rewrittenCnf certificate conflict ->
    exitCode ->
    ay_pger_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_pger_disj_right
    (ay_pger_ExitCodeSound exitCode (ay_pger_Sat originalCnf originalModel))
    (ay_pger_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))
    (ay_pger_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      exit
      (fun cert original =>
        ay_pger_unsat_pushback
          originalCnf rewrittenCnf detectedGate encodingClauses
          detectionWitness gateOutput representativeVariable
          representativeWitness gateClauses coveredClauses coverageWitness
          rewrittenModel originalModel certificate conflict gateDigest
          manifestDigest gateCertificate checkerAccepted originalFingerprint
          rewrittenFingerprint fingerprintWitness accepted replay cert original))

theorem ay_pger_failure_false_gate_detection
    (falseGateDetection : Prop) (missingRepresentative : Prop)
    (clauseCoverageGap : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    falseGateDetection ->
    ay_pger_GateFailure
      falseGateDetection missingRepresentative clauseCoverageGap
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro false_gate
  exact ay_pger_disj_left falseGateDetection
    (ay_pger_Disj missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)))))
    false_gate

theorem ay_pger_failure_missing_representative
    (falseGateDetection : Prop) (missingRepresentative : Prop)
    (clauseCoverageGap : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    missingRepresentative ->
    ay_pger_GateFailure
      falseGateDetection missingRepresentative clauseCoverageGap
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro missing
  exact ay_pger_disj_right falseGateDetection
    (ay_pger_Disj missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)))))
    (ay_pger_disj_left missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift))))
      missing)

theorem ay_pger_failure_clause_coverage_gap
    (falseGateDetection : Prop) (missingRepresentative : Prop)
    (clauseCoverageGap : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    clauseCoverageGap ->
    ay_pger_GateFailure
      falseGateDetection missingRepresentative clauseCoverageGap
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro gap
  exact ay_pger_disj_right falseGateDetection
    (ay_pger_Disj missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)))))
    (ay_pger_disj_right missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift))))
      (ay_pger_disj_left clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)))
        gap))

theorem ay_pger_failure_broken_reconstruction
    (falseGateDetection : Prop) (missingRepresentative : Prop)
    (clauseCoverageGap : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    brokenReconstruction ->
    ay_pger_GateFailure
      falseGateDetection missingRepresentative clauseCoverageGap
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro broken
  exact ay_pger_disj_right falseGateDetection
    (ay_pger_Disj missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)))))
    (ay_pger_disj_right missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift))))
      (ay_pger_disj_right clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)))
        (ay_pger_disj_left brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift))
          broken)))

theorem ay_pger_failure_digest_mismatch
    (falseGateDetection : Prop) (missingRepresentative : Prop)
    (clauseCoverageGap : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    digestMismatch ->
    ay_pger_GateFailure
      falseGateDetection missingRepresentative clauseCoverageGap
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro mismatch
  exact ay_pger_disj_right falseGateDetection
    (ay_pger_Disj missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)))))
    (ay_pger_disj_right missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift))))
      (ay_pger_disj_right clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)))
        (ay_pger_disj_right brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift))
          (ay_pger_disj_left digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)
            mismatch))))

theorem ay_pger_failure_replay_rejected
    (falseGateDetection : Prop) (missingRepresentative : Prop)
    (clauseCoverageGap : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    replayRejected ->
    ay_pger_GateFailure
      falseGateDetection missingRepresentative clauseCoverageGap
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro rejected
  exact ay_pger_disj_right falseGateDetection
    (ay_pger_Disj missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)))))
    (ay_pger_disj_right missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift))))
      (ay_pger_disj_right clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)))
        (ay_pger_disj_right brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift))
          (ay_pger_disj_right digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)
            (ay_pger_disj_left replayRejected fingerprintDrift rejected)))))

theorem ay_pger_failure_fingerprint_drift
    (falseGateDetection : Prop) (missingRepresentative : Prop)
    (clauseCoverageGap : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) :
    fingerprintDrift ->
    ay_pger_GateFailure
      falseGateDetection missingRepresentative clauseCoverageGap
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro drift
  exact ay_pger_disj_right falseGateDetection
    (ay_pger_Disj missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)))))
    (ay_pger_disj_right missingRepresentative
      (ay_pger_Disj clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift))))
      (ay_pger_disj_right clauseCoverageGap
        (ay_pger_Disj brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)))
        (ay_pger_disj_right brokenReconstruction
          (ay_pger_Disj digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift))
          (ay_pger_disj_right digestMismatch
            (ay_pger_Disj replayRejected fingerprintDrift)
            (ay_pger_disj_right replayRejected fingerprintDrift drift)))))

theorem ay_pger_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (falseGateDetection : Prop) (missingRepresentative : Prop)
    (clauseCoverageGap : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pger_DiagnosticGateLogEntry
      previousLog nextLog currentCnf falseGateDetection missingRepresentative
      clauseCoverageGap brokenReconstruction digestMismatch replayRejected
      fingerprintDrift recompute diagnostic ->
    ay_pger_GateFailure
      falseGateDetection missingRepresentative clauseCoverageGap
      brokenReconstruction digestMismatch replayRejected fingerprintDrift := by
  intro entry
  exact entry
    (ay_pger_GateFailure
      falseGateDetection missingRepresentative clauseCoverageGap
      brokenReconstruction digestMismatch replayRejected fingerprintDrift)
    (fun _previous rest1 =>
      rest1
        (ay_pger_GateFailure
          falseGateDetection missingRepresentative clauseCoverageGap
          brokenReconstruction digestMismatch replayRejected fingerprintDrift)
        (fun body _next =>
          body
            (ay_pger_GateFailure
              falseGateDetection missingRepresentative clauseCoverageGap
              brokenReconstruction digestMismatch replayRejected fingerprintDrift)
            (fun failure _tail => failure)))

theorem ay_pger_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (falseGateDetection : Prop) (missingRepresentative : Prop)
    (clauseCoverageGap : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pger_DiagnosticGateLogEntry
      previousLog nextLog currentCnf falseGateDetection missingRepresentative
      clauseCoverageGap brokenReconstruction digestMismatch replayRejected
      fingerprintDrift recompute diagnostic ->
    ay_pger_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_pger_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_pger_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_pger_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_pger_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_pger_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (falseGateDetection : Prop) (missingRepresentative : Prop)
    (clauseCoverageGap : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_pger_DiagnosticGateLogEntry
      previousLog nextLog currentCnf falseGateDetection missingRepresentative
      clauseCoverageGap brokenReconstruction digestMismatch replayRejected
      fingerprintDrift recompute diagnostic ->
    ay_pger_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_pger_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_pger_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_pger_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_pger_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_pger_failure_no_claim
    (falseGateDetection : Prop) (missingRepresentative : Prop)
    (clauseCoverageGap : Prop) (brokenReconstruction : Prop)
    (digestMismatch : Prop) (replayRejected : Prop)
    (fingerprintDrift : Prop) (diagnostic : Prop) :
    ay_pger_GateFailure
      falseGateDetection missingRepresentative clauseCoverageGap
      brokenReconstruction digestMismatch replayRejected fingerprintDrift ->
    diagnostic ->
    ay_pger_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
