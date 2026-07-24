-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Variable-elimination extension-certificate soundness for preprocessing.
-- The propositions stand for eliminated-variable definitions, extension maps,
-- equisatisfiability witnesses, reconstruction maps, formula fingerprints,
-- manifest digests, checker replay, diagnostics, and public SAT/UNSAT reports.

def ay_peec_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_peec_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_peec_Equisat (before : Prop) (after : Prop) :=
  ay_peec_Conj (before -> after) (after -> before)

def ay_peec_Sat (cnf : Prop) (model : Prop) :=
  ay_peec_Conj cnf model

def ay_peec_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_peec_IdMatch (leftId : Prop) (rightId : Prop) :=
  ay_peec_Conj (leftId -> rightId) (rightId -> leftId)

def ay_peec_EliminatedDefinitions
    (definitions : Prop) (definitionWitness : Prop) :=
  ay_peec_Conj definitions definitionWitness

def ay_peec_ExtensionMap
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (extensionWitness : Prop) :=
  ay_peec_Conj extensionWitness
    (ay_peec_Sat reducedCnf reducedModel ->
      ay_peec_Sat originalCnf originalModel)

def ay_peec_ModelReconstruction
    (reducedCnf : Prop) (originalCnf : Prop)
    (reducedModel : Prop) (originalModel : Prop) :=
  ay_peec_Sat reducedCnf reducedModel ->
    ay_peec_Sat originalCnf originalModel

def ay_peec_ProofReconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_peec_Replay reducedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_peec_FingerprintAgreement
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop) :=
  ay_peec_Conj lineageWitness
    (ay_peec_IdMatch originalFingerprint reducedFingerprint)

def ay_peec_DigestAgreement
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop) :=
  ay_peec_Conj digestWitness
    (ay_peec_IdMatch manifestDigest certificateDigest)

def ay_peec_CheckerReplay
    (certificateBundle : Prop) (checkerAccepted : Prop) :=
  ay_peec_Conj certificateBundle checkerAccepted

def ay_peec_EliminationExtensionCertificate
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :=
  ay_peec_Conj
    (ay_peec_EliminatedDefinitions definitions definitionWitness)
    (ay_peec_Conj
      (ay_peec_ExtensionMap
        reducedCnf originalCnf reducedModel originalModel
        extensionWitness)
      (ay_peec_Conj
        (ay_peec_Equisat originalCnf reducedCnf)
        (ay_peec_Conj
          (ay_peec_ModelReconstruction
            reducedCnf originalCnf reducedModel originalModel)
          (ay_peec_Conj
            (ay_peec_ProofReconstruction
              originalCnf reducedCnf certificate conflict)
            (ay_peec_Conj
              (ay_peec_FingerprintAgreement
                originalFingerprint reducedFingerprint lineageWitness)
              (ay_peec_Conj
                (ay_peec_DigestAgreement
                  manifestDigest certificateDigest digestWitness)
                (ay_peec_CheckerReplay
                  certificateBundle checkerAccepted)))))))

def ay_peec_AcceptedCertificateLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :=
  ay_peec_Conj previousLog
    (ay_peec_Conj
      (ay_peec_EliminationExtensionCertificate
        originalCnf reducedCnf definitions definitionWitness
        extensionWitness reducedModel originalModel certificate conflict
        originalFingerprint reducedFingerprint lineageWitness
        manifestDigest certificateDigest digestWitness certificateBundle
        checkerAccepted)
      nextLog)

def ay_peec_CertificateFailure
    (missingDefinitions : Prop) (staleExtensionMap : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :=
  ay_peec_Disj missingDefinitions
    (ay_peec_Disj staleExtensionMap
      (ay_peec_Disj fingerprintMismatch
        (ay_peec_Disj digestMismatch replayRejected)))

def ay_peec_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_peec_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_peec_Conj currentCnf recompute

def ay_peec_DiagnosticCertificateLogEntry
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingDefinitions : Prop) (staleExtensionMap : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_peec_Conj previousLog
    (ay_peec_Conj
      (ay_peec_Conj
        (ay_peec_CertificateFailure
          missingDefinitions staleExtensionMap fingerprintMismatch
          digestMismatch replayRejected)
        (ay_peec_Conj
          (ay_peec_RecomputeObligation currentCnf recompute)
          (ay_peec_NoSemanticClaim diagnostic)))
      nextLog)

def ay_peec_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_peec_Conj exitCode claim

def ay_peec_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_peec_Disj
    (ay_peec_ExitCodeSound exitCode (ay_peec_Sat originalCnf model))
    (ay_peec_ExitCodeSound exitCode (certificate -> originalCnf -> conflict))

theorem ay_peec_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_peec_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_peec_conj_left
    (left : Prop) (right : Prop) :
    ay_peec_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_peec_conj_right
    (left : Prop) (right : Prop) :
    ay_peec_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_peec_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_peec_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_peec_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_peec_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_peec_equisat_forward
    (before : Prop) (after : Prop) :
    ay_peec_Equisat before after ->
    before ->
    after := by
  intro eq
  exact ay_peec_conj_left (before -> after) (after -> before) eq

theorem ay_peec_equisat_backward
    (before : Prop) (after : Prop) :
    ay_peec_Equisat before after ->
    after ->
    before := by
  intro eq
  exact ay_peec_conj_right (before -> after) (after -> before) eq

theorem ay_peec_certificate_definitions
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_peec_EliminationExtensionCertificate
      originalCnf reducedCnf definitions definitionWitness
      extensionWitness reducedModel originalModel certificate conflict
      originalFingerprint reducedFingerprint lineageWitness
      manifestDigest certificateDigest digestWitness certificateBundle
      checkerAccepted ->
    ay_peec_EliminatedDefinitions definitions definitionWitness := by
  intro accepted
  exact ay_peec_conj_left
    (ay_peec_EliminatedDefinitions definitions definitionWitness)
    (ay_peec_Conj
      (ay_peec_ExtensionMap
        reducedCnf originalCnf reducedModel originalModel extensionWitness)
      (ay_peec_Conj
        (ay_peec_Equisat originalCnf reducedCnf)
        (ay_peec_Conj
          (ay_peec_ModelReconstruction
            reducedCnf originalCnf reducedModel originalModel)
          (ay_peec_Conj
            (ay_peec_ProofReconstruction
              originalCnf reducedCnf certificate conflict)
            (ay_peec_Conj
              (ay_peec_FingerprintAgreement
                originalFingerprint reducedFingerprint lineageWitness)
              (ay_peec_Conj
                (ay_peec_DigestAgreement
                  manifestDigest certificateDigest digestWitness)
                (ay_peec_CheckerReplay
                  certificateBundle checkerAccepted)))))))
    accepted

theorem ay_peec_certificate_extension
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_peec_EliminationExtensionCertificate
      originalCnf reducedCnf definitions definitionWitness
      extensionWitness reducedModel originalModel certificate conflict
      originalFingerprint reducedFingerprint lineageWitness
      manifestDigest certificateDigest digestWitness certificateBundle
      checkerAccepted ->
    ay_peec_ExtensionMap
      reducedCnf originalCnf reducedModel originalModel extensionWitness := by
  intro accepted
  exact accepted
    (ay_peec_ExtensionMap
      reducedCnf originalCnf reducedModel originalModel extensionWitness)
    (fun _defs rest1 =>
      rest1
        (ay_peec_ExtensionMap
          reducedCnf originalCnf reducedModel originalModel extensionWitness)
        (fun ext _tail => ext))

theorem ay_peec_certificate_equisat
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_peec_EliminationExtensionCertificate
      originalCnf reducedCnf definitions definitionWitness
      extensionWitness reducedModel originalModel certificate conflict
      originalFingerprint reducedFingerprint lineageWitness
      manifestDigest certificateDigest digestWitness certificateBundle
      checkerAccepted ->
    ay_peec_Equisat originalCnf reducedCnf := by
  intro accepted
  exact accepted
    (ay_peec_Equisat originalCnf reducedCnf)
    (fun _defs rest1 =>
      rest1
        (ay_peec_Equisat originalCnf reducedCnf)
        (fun _ext rest2 =>
          rest2
            (ay_peec_Equisat originalCnf reducedCnf)
            (fun eq _tail => eq)))

theorem ay_peec_certificate_model_reconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_peec_EliminationExtensionCertificate
      originalCnf reducedCnf definitions definitionWitness
      extensionWitness reducedModel originalModel certificate conflict
      originalFingerprint reducedFingerprint lineageWitness
      manifestDigest certificateDigest digestWitness certificateBundle
      checkerAccepted ->
    ay_peec_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel := by
  intro accepted
  exact accepted
    (ay_peec_ModelReconstruction
      reducedCnf originalCnf reducedModel originalModel)
    (fun _defs rest1 =>
      rest1
        (ay_peec_ModelReconstruction
          reducedCnf originalCnf reducedModel originalModel)
        (fun _ext rest2 =>
          rest2
            (ay_peec_ModelReconstruction
              reducedCnf originalCnf reducedModel originalModel)
            (fun _eq rest3 =>
              rest3
                (ay_peec_ModelReconstruction
                  reducedCnf originalCnf reducedModel originalModel)
                (fun model _tail => model))))

theorem ay_peec_certificate_proof_reconstruction
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_peec_EliminationExtensionCertificate
      originalCnf reducedCnf definitions definitionWitness
      extensionWitness reducedModel originalModel certificate conflict
      originalFingerprint reducedFingerprint lineageWitness
      manifestDigest certificateDigest digestWitness certificateBundle
      checkerAccepted ->
    ay_peec_ProofReconstruction originalCnf reducedCnf certificate conflict := by
  intro accepted
  exact accepted
    (ay_peec_ProofReconstruction originalCnf reducedCnf certificate conflict)
    (fun _defs rest1 =>
      rest1
        (ay_peec_ProofReconstruction
          originalCnf reducedCnf certificate conflict)
        (fun _ext rest2 =>
          rest2
            (ay_peec_ProofReconstruction
              originalCnf reducedCnf certificate conflict)
            (fun _eq rest3 =>
              rest3
                (ay_peec_ProofReconstruction
                  originalCnf reducedCnf certificate conflict)
                (fun _model rest4 =>
                  rest4
                    (ay_peec_ProofReconstruction
                      originalCnf reducedCnf certificate conflict)
                    (fun proof _tail => proof)))))

theorem ay_peec_certificate_fingerprint
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_peec_EliminationExtensionCertificate
      originalCnf reducedCnf definitions definitionWitness
      extensionWitness reducedModel originalModel certificate conflict
      originalFingerprint reducedFingerprint lineageWitness
      manifestDigest certificateDigest digestWitness certificateBundle
      checkerAccepted ->
    ay_peec_FingerprintAgreement
      originalFingerprint reducedFingerprint lineageWitness := by
  intro accepted
  exact accepted
    (ay_peec_FingerprintAgreement
      originalFingerprint reducedFingerprint lineageWitness)
    (fun _defs rest1 =>
      rest1
        (ay_peec_FingerprintAgreement
          originalFingerprint reducedFingerprint lineageWitness)
        (fun _ext rest2 =>
          rest2
            (ay_peec_FingerprintAgreement
              originalFingerprint reducedFingerprint lineageWitness)
            (fun _eq rest3 =>
              rest3
                (ay_peec_FingerprintAgreement
                  originalFingerprint reducedFingerprint lineageWitness)
                (fun _model rest4 =>
                  rest4
                    (ay_peec_FingerprintAgreement
                      originalFingerprint reducedFingerprint lineageWitness)
                    (fun _proof rest5 =>
                      rest5
                        (ay_peec_FingerprintAgreement
                          originalFingerprint reducedFingerprint lineageWitness)
                        (fun fp _tail => fp))))))

theorem ay_peec_certificate_digest
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_peec_EliminationExtensionCertificate
      originalCnf reducedCnf definitions definitionWitness
      extensionWitness reducedModel originalModel certificate conflict
      originalFingerprint reducedFingerprint lineageWitness
      manifestDigest certificateDigest digestWitness certificateBundle
      checkerAccepted ->
    ay_peec_DigestAgreement
      manifestDigest certificateDigest digestWitness := by
  intro accepted
  exact accepted
    (ay_peec_DigestAgreement manifestDigest certificateDigest digestWitness)
    (fun _defs rest1 =>
      rest1
        (ay_peec_DigestAgreement manifestDigest certificateDigest digestWitness)
        (fun _ext rest2 =>
          rest2
            (ay_peec_DigestAgreement manifestDigest certificateDigest digestWitness)
            (fun _eq rest3 =>
              rest3
                (ay_peec_DigestAgreement
                  manifestDigest certificateDigest digestWitness)
                (fun _model rest4 =>
                  rest4
                    (ay_peec_DigestAgreement
                      manifestDigest certificateDigest digestWitness)
                    (fun _proof rest5 =>
                      rest5
                        (ay_peec_DigestAgreement
                          manifestDigest certificateDigest digestWitness)
                        (fun _fp rest6 =>
                          rest6
                            (ay_peec_DigestAgreement
                              manifestDigest certificateDigest digestWitness)
                            (fun digest _tail => digest)))))))

theorem ay_peec_certificate_checker_replay
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_peec_EliminationExtensionCertificate
      originalCnf reducedCnf definitions definitionWitness
      extensionWitness reducedModel originalModel certificate conflict
      originalFingerprint reducedFingerprint lineageWitness
      manifestDigest certificateDigest digestWitness certificateBundle
      checkerAccepted ->
    ay_peec_CheckerReplay certificateBundle checkerAccepted := by
  intro accepted
  exact accepted
    (ay_peec_CheckerReplay certificateBundle checkerAccepted)
    (fun _defs rest1 =>
      rest1
        (ay_peec_CheckerReplay certificateBundle checkerAccepted)
        (fun _ext rest2 =>
          rest2
            (ay_peec_CheckerReplay certificateBundle checkerAccepted)
            (fun _eq rest3 =>
              rest3
                (ay_peec_CheckerReplay certificateBundle checkerAccepted)
                (fun _model rest4 =>
                  rest4
                    (ay_peec_CheckerReplay certificateBundle checkerAccepted)
                    (fun _proof rest5 =>
                      rest5
                        (ay_peec_CheckerReplay certificateBundle checkerAccepted)
                        (fun _fp rest6 =>
                          rest6
                            (ay_peec_CheckerReplay
                              certificateBundle checkerAccepted)
                            (fun _digest replay => replay)))))))

theorem ay_peec_extension_sat_pullback
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_peec_EliminationExtensionCertificate
      originalCnf reducedCnf definitions definitionWitness
      extensionWitness reducedModel originalModel certificate conflict
      originalFingerprint reducedFingerprint lineageWitness
      manifestDigest certificateDigest digestWitness certificateBundle
      checkerAccepted ->
    ay_peec_Sat reducedCnf reducedModel ->
    ay_peec_Sat originalCnf originalModel := by
  intro accepted reducedSat
  exact
    (ay_peec_certificate_model_reconstruction
      originalCnf reducedCnf definitions definitionWitness extensionWitness
      reducedModel originalModel certificate conflict originalFingerprint
      reducedFingerprint lineageWitness manifestDigest certificateDigest
      digestWitness certificateBundle checkerAccepted accepted)
      reducedSat

theorem ay_peec_replay_unsat_pushback
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop) :
    ay_peec_EliminationExtensionCertificate
      originalCnf reducedCnf definitions definitionWitness
      extensionWitness reducedModel originalModel certificate conflict
      originalFingerprint reducedFingerprint lineageWitness
      manifestDigest certificateDigest digestWitness certificateBundle
      checkerAccepted ->
    ay_peec_Replay reducedCnf certificate conflict ->
    certificate ->
    originalCnf ->
    conflict := by
  intro accepted replay cert original
  exact
    (ay_peec_certificate_proof_reconstruction
      originalCnf reducedCnf definitions definitionWitness extensionWitness
      reducedModel originalModel certificate conflict originalFingerprint
      reducedFingerprint lineageWitness manifestDigest certificateDigest
      digestWitness certificateBundle checkerAccepted accepted)
      replay cert original

theorem ay_peec_public_sat
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop)
    (exitCode : Prop) :
    ay_peec_EliminationExtensionCertificate
      originalCnf reducedCnf definitions definitionWitness
      extensionWitness reducedModel originalModel certificate conflict
      originalFingerprint reducedFingerprint lineageWitness
      manifestDigest certificateDigest digestWitness certificateBundle
      checkerAccepted ->
    ay_peec_Sat reducedCnf reducedModel ->
    exitCode ->
    ay_peec_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted reducedSat exit
  exact ay_peec_disj_left
    (ay_peec_ExitCodeSound exitCode (ay_peec_Sat originalCnf originalModel))
    (ay_peec_ExitCodeSound
      exitCode (certificate -> originalCnf -> conflict))
    (ay_peec_conj_intro exitCode
      (ay_peec_Sat originalCnf originalModel)
      exit
      (ay_peec_extension_sat_pullback
        originalCnf reducedCnf definitions definitionWitness extensionWitness
        reducedModel originalModel certificate conflict originalFingerprint
        reducedFingerprint lineageWitness manifestDigest certificateDigest
        digestWitness certificateBundle checkerAccepted accepted reducedSat))

theorem ay_peec_public_unsat
    (originalCnf : Prop) (reducedCnf : Prop)
    (definitions : Prop) (definitionWitness : Prop)
    (extensionWitness : Prop)
    (reducedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (originalFingerprint : Prop) (reducedFingerprint : Prop)
    (lineageWitness : Prop)
    (manifestDigest : Prop) (certificateDigest : Prop)
    (digestWitness : Prop)
    (certificateBundle : Prop) (checkerAccepted : Prop)
    (exitCode : Prop) :
    ay_peec_EliminationExtensionCertificate
      originalCnf reducedCnf definitions definitionWitness
      extensionWitness reducedModel originalModel certificate conflict
      originalFingerprint reducedFingerprint lineageWitness
      manifestDigest certificateDigest digestWitness certificateBundle
      checkerAccepted ->
    ay_peec_Replay reducedCnf certificate conflict ->
    exitCode ->
    ay_peec_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro accepted replay exit
  exact ay_peec_disj_right
    (ay_peec_ExitCodeSound exitCode (ay_peec_Sat originalCnf originalModel))
    (ay_peec_ExitCodeSound
      exitCode (certificate -> originalCnf -> conflict))
    (ay_peec_conj_intro exitCode
      (certificate -> originalCnf -> conflict)
      exit
      (fun cert original =>
        ay_peec_replay_unsat_pushback
          originalCnf reducedCnf definitions definitionWitness extensionWitness
          reducedModel originalModel certificate conflict originalFingerprint
          reducedFingerprint lineageWitness manifestDigest certificateDigest
          digestWitness certificateBundle checkerAccepted accepted replay cert
          original))

theorem ay_peec_failure_missing_definitions
    (missingDefinitions : Prop) (staleExtensionMap : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    missingDefinitions ->
    ay_peec_CertificateFailure
      missingDefinitions staleExtensionMap fingerprintMismatch
      digestMismatch replayRejected := by
  intro missing
  exact ay_peec_disj_left missingDefinitions
    (ay_peec_Disj staleExtensionMap
      (ay_peec_Disj fingerprintMismatch
        (ay_peec_Disj digestMismatch replayRejected)))
    missing

theorem ay_peec_failure_stale_extension
    (missingDefinitions : Prop) (staleExtensionMap : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    staleExtensionMap ->
    ay_peec_CertificateFailure
      missingDefinitions staleExtensionMap fingerprintMismatch
      digestMismatch replayRejected := by
  intro stale
  exact ay_peec_disj_right missingDefinitions
    (ay_peec_Disj staleExtensionMap
      (ay_peec_Disj fingerprintMismatch
        (ay_peec_Disj digestMismatch replayRejected)))
    (ay_peec_disj_left staleExtensionMap
      (ay_peec_Disj fingerprintMismatch
        (ay_peec_Disj digestMismatch replayRejected))
      stale)

theorem ay_peec_failure_fingerprint_mismatch
    (missingDefinitions : Prop) (staleExtensionMap : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    fingerprintMismatch ->
    ay_peec_CertificateFailure
      missingDefinitions staleExtensionMap fingerprintMismatch
      digestMismatch replayRejected := by
  intro mismatch
  exact ay_peec_disj_right missingDefinitions
    (ay_peec_Disj staleExtensionMap
      (ay_peec_Disj fingerprintMismatch
        (ay_peec_Disj digestMismatch replayRejected)))
    (ay_peec_disj_right staleExtensionMap
      (ay_peec_Disj fingerprintMismatch
        (ay_peec_Disj digestMismatch replayRejected))
      (ay_peec_disj_left fingerprintMismatch
        (ay_peec_Disj digestMismatch replayRejected)
        mismatch))

theorem ay_peec_failure_digest_mismatch
    (missingDefinitions : Prop) (staleExtensionMap : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    digestMismatch ->
    ay_peec_CertificateFailure
      missingDefinitions staleExtensionMap fingerprintMismatch
      digestMismatch replayRejected := by
  intro mismatch
  exact ay_peec_disj_right missingDefinitions
    (ay_peec_Disj staleExtensionMap
      (ay_peec_Disj fingerprintMismatch
        (ay_peec_Disj digestMismatch replayRejected)))
    (ay_peec_disj_right staleExtensionMap
      (ay_peec_Disj fingerprintMismatch
        (ay_peec_Disj digestMismatch replayRejected))
      (ay_peec_disj_right fingerprintMismatch
        (ay_peec_Disj digestMismatch replayRejected)
        (ay_peec_disj_left digestMismatch replayRejected mismatch)))

theorem ay_peec_failure_replay_rejected
    (missingDefinitions : Prop) (staleExtensionMap : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) :
    replayRejected ->
    ay_peec_CertificateFailure
      missingDefinitions staleExtensionMap fingerprintMismatch
      digestMismatch replayRejected := by
  intro rejected
  exact ay_peec_disj_right missingDefinitions
    (ay_peec_Disj staleExtensionMap
      (ay_peec_Disj fingerprintMismatch
        (ay_peec_Disj digestMismatch replayRejected)))
    (ay_peec_disj_right staleExtensionMap
      (ay_peec_Disj fingerprintMismatch
        (ay_peec_Disj digestMismatch replayRejected))
      (ay_peec_disj_right fingerprintMismatch
        (ay_peec_Disj digestMismatch replayRejected)
        (ay_peec_disj_right digestMismatch replayRejected rejected)))

theorem ay_peec_diagnostic_failure
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingDefinitions : Prop) (staleExtensionMap : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_peec_DiagnosticCertificateLogEntry
      previousLog nextLog currentCnf missingDefinitions staleExtensionMap
      fingerprintMismatch digestMismatch replayRejected recompute diagnostic ->
    ay_peec_CertificateFailure
      missingDefinitions staleExtensionMap fingerprintMismatch
      digestMismatch replayRejected := by
  intro entry
  exact entry
    (ay_peec_CertificateFailure
      missingDefinitions staleExtensionMap fingerprintMismatch
      digestMismatch replayRejected)
    (fun _previous rest1 =>
      rest1
        (ay_peec_CertificateFailure
          missingDefinitions staleExtensionMap fingerprintMismatch
          digestMismatch replayRejected)
        (fun body _next =>
          body
            (ay_peec_CertificateFailure
              missingDefinitions staleExtensionMap fingerprintMismatch
              digestMismatch replayRejected)
            (fun failure _tail => failure)))

theorem ay_peec_diagnostic_no_claim
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingDefinitions : Prop) (staleExtensionMap : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_peec_DiagnosticCertificateLogEntry
      previousLog nextLog currentCnf missingDefinitions staleExtensionMap
      fingerprintMismatch digestMismatch replayRejected recompute diagnostic ->
    ay_peec_NoSemanticClaim diagnostic := by
  intro entry
  exact entry
    (ay_peec_NoSemanticClaim diagnostic)
    (fun _previous rest1 =>
      rest1
        (ay_peec_NoSemanticClaim diagnostic)
        (fun body _next =>
          body
            (ay_peec_NoSemanticClaim diagnostic)
            (fun _failure rest2 =>
              rest2
                (ay_peec_NoSemanticClaim diagnostic)
                (fun _recompute no_claim => no_claim))))

theorem ay_peec_diagnostic_recompute
    (previousLog : Prop) (nextLog : Prop)
    (currentCnf : Prop)
    (missingDefinitions : Prop) (staleExtensionMap : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_peec_DiagnosticCertificateLogEntry
      previousLog nextLog currentCnf missingDefinitions staleExtensionMap
      fingerprintMismatch digestMismatch replayRejected recompute diagnostic ->
    ay_peec_RecomputeObligation currentCnf recompute := by
  intro entry
  exact entry
    (ay_peec_RecomputeObligation currentCnf recompute)
    (fun _previous rest1 =>
      rest1
        (ay_peec_RecomputeObligation currentCnf recompute)
        (fun body _next =>
          body
            (ay_peec_RecomputeObligation currentCnf recompute)
            (fun _failure rest2 =>
              rest2
                (ay_peec_RecomputeObligation currentCnf recompute)
                (fun recompute_obligation _no_claim =>
                  recompute_obligation))))

theorem ay_peec_failure_no_claim
    (missingDefinitions : Prop) (staleExtensionMap : Prop)
    (fingerprintMismatch : Prop) (digestMismatch : Prop)
    (replayRejected : Prop) (diagnostic : Prop) :
    ay_peec_CertificateFailure
      missingDefinitions staleExtensionMap fingerprintMismatch
      digestMismatch replayRejected ->
    diagnostic ->
    ay_peec_NoSemanticClaim diagnostic := by
  intro _failure diag
  exact diag
