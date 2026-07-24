-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Binary-clause closure preprocessing guard soundness.
-- The propositions stand for formula digests, binary implication graph digests,
-- closure-edge ledgers, implied-clause witnesses, model/proof reconstruction,
-- fallback/build/validator gates, audit transcripts, diagnostics, and public
-- SAT/UNSAT reports.

def ay_bccg_Conj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def ay_bccg_Disj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_bccg_Equisat (original : Prop) (closed : Prop) :=
  ay_bccg_Conj (original -> closed) (closed -> original)

def ay_bccg_Sat (cnf : Prop) (model : Prop) :=
  ay_bccg_Conj cnf model

def ay_bccg_Replay (cnf : Prop) (certificate : Prop) (conflict : Prop) :=
  cnf -> certificate -> conflict

def ay_bccg_OriginalFormulaDigest
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :=
  ay_bccg_Conj formulaManifest (formulaDigest -> formulaDigestAccepted)

def ay_bccg_BinaryImplicationGraphDigest
    (graphDigest : Prop) (graphAccepted : Prop)
    (graphManifest : Prop) :=
  ay_bccg_Conj graphManifest (graphDigest -> graphAccepted)

def ay_bccg_ClosureEdgeLedger
    (closureEdgeLedger : Prop) (edgeAccepted : Prop)
    (edgeCoverage : Prop) :=
  ay_bccg_Conj edgeCoverage (closureEdgeLedger -> edgeAccepted)

def ay_bccg_ImpliedClauseWitness
    (impliedClauseWitness : Prop) (impliedAccepted : Prop)
    (impliedCoverage : Prop) :=
  ay_bccg_Conj impliedCoverage (impliedClauseWitness -> impliedAccepted)

def ay_bccg_ModelReconstructionWitness
    (closedCnf : Prop) (originalCnf : Prop)
    (closedModel : Prop) (originalModel : Prop) :=
  ay_bccg_Sat closedCnf closedModel ->
    ay_bccg_Sat originalCnf originalModel

def ay_bccg_UnsatProofReconstructionWitness
    (originalCnf : Prop) (closedCnf : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bccg_Replay closedCnf certificate conflict ->
    certificate -> originalCnf -> conflict

def ay_bccg_ReconstructionWitnesses
    (closedCnf : Prop) (originalCnf : Prop)
    (closedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :=
  ay_bccg_Conj
    (ay_bccg_ModelReconstructionWitness
      closedCnf originalCnf closedModel originalModel)
    (ay_bccg_UnsatProofReconstructionWitness
      originalCnf closedCnf certificate conflict)

def ay_bccg_FallbackBaseline
    (baselineSolver : Prop) (baselineAvailable : Prop) :=
  ay_bccg_Conj baselineSolver baselineAvailable

def ay_bccg_BuildEvidence
    (binaryFingerprint : Prop) (buildReproducible : Prop) :=
  ay_bccg_Conj binaryFingerprint buildReproducible

def ay_bccg_ValidatorGate
    (validatorAccepted : Prop) (validatorVersion : Prop) :=
  ay_bccg_Conj validatorAccepted validatorVersion

def ay_bccg_AuditTranscript
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  ay_bccg_Conj auditAppended auditAppendOnly

def ay_bccg_AcceptedBinaryClauseClosureGuard
    (originalCnf : Prop) (closedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (graphDigest : Prop) (graphAccepted : Prop)
    (graphManifest : Prop)
    (closureEdgeLedger : Prop) (edgeAccepted : Prop)
    (edgeCoverage : Prop)
    (impliedClauseWitness : Prop) (impliedAccepted : Prop)
    (impliedCoverage : Prop)
    (closedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :=
  forall result : Prop,
    (ay_bccg_OriginalFormulaDigest
       formulaDigest formulaDigestAccepted formulaManifest ->
     ay_bccg_BinaryImplicationGraphDigest
       graphDigest graphAccepted graphManifest ->
     ay_bccg_ClosureEdgeLedger
       closureEdgeLedger edgeAccepted edgeCoverage ->
     ay_bccg_ImpliedClauseWitness
       impliedClauseWitness impliedAccepted impliedCoverage ->
     ay_bccg_ReconstructionWitnesses
       closedCnf originalCnf closedModel originalModel certificate conflict ->
     ay_bccg_Equisat originalCnf closedCnf ->
     ay_bccg_FallbackBaseline baselineSolver baselineAvailable ->
     ay_bccg_BuildEvidence binaryFingerprint buildReproducible ->
     ay_bccg_ValidatorGate validatorAccepted validatorVersion ->
     ay_bccg_AuditTranscript auditAppended auditAppendOnly ->
     result) -> result

def ay_bccg_BinaryClauseClosureGuardFailure
    (digestMismatch : Prop) (graphMismatch : Prop)
    (edgeMismatch : Prop) (impliedMismatch : Prop)
    (reconstructionMismatch : Prop) (baselineMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop) :=
  forall result : Prop,
    (digestMismatch -> result) ->
    (graphMismatch -> result) ->
    (edgeMismatch -> result) ->
    (impliedMismatch -> result) ->
    (reconstructionMismatch -> result) ->
    (baselineMismatch -> result) ->
    (buildMismatch -> result) ->
    (validatorMismatch -> result) ->
    (auditMismatch -> result) ->
    result

def ay_bccg_NoSemanticClaim (diagnostic : Prop) :=
  diagnostic

def ay_bccg_RecomputeObligation (currentCnf : Prop) (recompute : Prop) :=
  ay_bccg_Conj currentCnf recompute

def ay_bccg_DiagnosticBinaryClauseClosureGuard
    (currentCnf : Prop)
    (digestMismatch : Prop) (graphMismatch : Prop)
    (edgeMismatch : Prop) (impliedMismatch : Prop)
    (reconstructionMismatch : Prop) (baselineMismatch : Prop)
    (buildMismatch : Prop) (validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :=
  ay_bccg_Conj
    (ay_bccg_BinaryClauseClosureGuardFailure
      digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch)
    (ay_bccg_Conj
      (ay_bccg_RecomputeObligation currentCnf recompute)
      (ay_bccg_NoSemanticClaim diagnostic))

def ay_bccg_ExitCodeSound (exitCode : Prop) (claim : Prop) :=
  ay_bccg_Conj exitCode claim

def ay_bccg_PublicResult
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :=
  ay_bccg_Disj
    (ay_bccg_ExitCodeSound exitCode (ay_bccg_Sat originalCnf model))
    (ay_bccg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))

theorem ay_bccg_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> ay_bccg_Conj left right := by
  intro hleft hright result build
  exact build hleft hright

theorem ay_bccg_conj_left
    (left : Prop) (right : Prop) :
    ay_bccg_Conj left right -> left := by
  intro both
  exact both left (fun hleft _hright => hleft)

theorem ay_bccg_conj_right
    (left : Prop) (right : Prop) :
    ay_bccg_Conj left right -> right := by
  intro both
  exact both right (fun _hleft hright => hright)

theorem ay_bccg_disj_left
    (left : Prop) (right : Prop) :
    left -> ay_bccg_Disj left right := by
  intro hleft result left_case _right_case
  exact left_case hleft

theorem ay_bccg_disj_right
    (left : Prop) (right : Prop) :
    right -> ay_bccg_Disj left right := by
  intro hright result _left_case right_case
  exact right_case hright

theorem ay_bccg_equisat_forward
    (original : Prop) (closed : Prop) :
    ay_bccg_Equisat original closed -> original -> closed := by
  intro eqsat
  exact ay_bccg_conj_left (original -> closed) (closed -> original) eqsat

theorem ay_bccg_equisat_backward
    (original : Prop) (closed : Prop) :
    ay_bccg_Equisat original closed -> closed -> original := by
  intro eqsat
  exact ay_bccg_conj_right (original -> closed) (closed -> original) eqsat

theorem ay_bccg_original_formula_digest_applies
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop) :
    ay_bccg_OriginalFormulaDigest
      formulaDigest formulaDigestAccepted formulaManifest ->
    formulaDigest -> formulaDigestAccepted := by
  intro digest
  exact ay_bccg_conj_right
    formulaManifest (formulaDigest -> formulaDigestAccepted) digest

theorem ay_bccg_binary_implication_graph_digest_applies
    (graphDigest : Prop) (graphAccepted : Prop)
    (graphManifest : Prop) :
    ay_bccg_BinaryImplicationGraphDigest
      graphDigest graphAccepted graphManifest ->
    graphDigest -> graphAccepted := by
  intro digest
  exact ay_bccg_conj_right
    graphManifest (graphDigest -> graphAccepted) digest

theorem ay_bccg_closure_edge_ledger_applies
    (closureEdgeLedger : Prop) (edgeAccepted : Prop)
    (edgeCoverage : Prop) :
    ay_bccg_ClosureEdgeLedger
      closureEdgeLedger edgeAccepted edgeCoverage ->
    closureEdgeLedger -> edgeAccepted := by
  intro ledger
  exact ay_bccg_conj_right
    edgeCoverage (closureEdgeLedger -> edgeAccepted) ledger

theorem ay_bccg_implied_clause_witness_applies
    (impliedClauseWitness : Prop) (impliedAccepted : Prop)
    (impliedCoverage : Prop) :
    ay_bccg_ImpliedClauseWitness
      impliedClauseWitness impliedAccepted impliedCoverage ->
    impliedClauseWitness -> impliedAccepted := by
  intro witness
  exact ay_bccg_conj_right
    impliedCoverage (impliedClauseWitness -> impliedAccepted) witness

theorem ay_bccg_model_reconstruction
    (closedCnf : Prop) (originalCnf : Prop)
    (closedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bccg_ReconstructionWitnesses
      closedCnf originalCnf closedModel originalModel certificate conflict ->
    ay_bccg_Sat closedCnf closedModel ->
    ay_bccg_Sat originalCnf originalModel := by
  intro witnesses
  exact ay_bccg_conj_left
    (ay_bccg_ModelReconstructionWitness
      closedCnf originalCnf closedModel originalModel)
    (ay_bccg_UnsatProofReconstructionWitness
      originalCnf closedCnf certificate conflict)
    witnesses

theorem ay_bccg_unsat_proof_reconstruction
    (closedCnf : Prop) (originalCnf : Prop)
    (closedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bccg_ReconstructionWitnesses
      closedCnf originalCnf closedModel originalModel certificate conflict ->
    ay_bccg_Replay closedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses
  exact ay_bccg_conj_right
    (ay_bccg_ModelReconstructionWitness
      closedCnf originalCnf closedModel originalModel)
    (ay_bccg_UnsatProofReconstructionWitness
      originalCnf closedCnf certificate conflict)
    witnesses

theorem ay_bccg_accepted_equisat
    (originalCnf : Prop) (closedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (graphDigest : Prop) (graphAccepted : Prop)
    (graphManifest : Prop)
    (closureEdgeLedger : Prop) (edgeAccepted : Prop)
    (edgeCoverage : Prop)
    (impliedClauseWitness : Prop) (impliedAccepted : Prop)
    (impliedCoverage : Prop)
    (closedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bccg_AcceptedBinaryClauseClosureGuard
      originalCnf closedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      graphDigest graphAccepted graphManifest
      closureEdgeLedger edgeAccepted edgeCoverage
      impliedClauseWitness impliedAccepted impliedCoverage
      closedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bccg_Equisat originalCnf closedCnf := by
  intro accepted
  exact accepted (ay_bccg_Equisat originalCnf closedCnf)
    (fun _digestOk _graphOk _edgeOk _impliedOk _reconstruct eqsat
      _fallback _build _validator _audit => eqsat)

theorem ay_bccg_accepted_reconstruction
    (originalCnf : Prop) (closedCnf : Prop)
    (formulaDigest : Prop) (formulaDigestAccepted : Prop)
    (formulaManifest : Prop)
    (graphDigest : Prop) (graphAccepted : Prop)
    (graphManifest : Prop)
    (closureEdgeLedger : Prop) (edgeAccepted : Prop)
    (edgeCoverage : Prop)
    (impliedClauseWitness : Prop) (impliedAccepted : Prop)
    (impliedCoverage : Prop)
    (closedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop)
    (baselineSolver : Prop) (baselineAvailable : Prop)
    (binaryFingerprint : Prop) (buildReproducible : Prop)
    (validatorAccepted : Prop) (validatorVersion : Prop)
    (auditAppended : Prop) (auditAppendOnly : Prop) :
    ay_bccg_AcceptedBinaryClauseClosureGuard
      originalCnf closedCnf
      formulaDigest formulaDigestAccepted formulaManifest
      graphDigest graphAccepted graphManifest
      closureEdgeLedger edgeAccepted edgeCoverage
      impliedClauseWitness impliedAccepted impliedCoverage
      closedModel originalModel certificate conflict
      baselineSolver baselineAvailable
      binaryFingerprint buildReproducible
      validatorAccepted validatorVersion auditAppended auditAppendOnly ->
    ay_bccg_ReconstructionWitnesses
      closedCnf originalCnf closedModel originalModel certificate conflict := by
  intro accepted
  exact accepted
    (ay_bccg_ReconstructionWitnesses
      closedCnf originalCnf closedModel originalModel certificate conflict)
    (fun _digestOk _graphOk _edgeOk _impliedOk reconstruct _eqsat
      _fallback _build _validator _audit => reconstruct)

theorem ay_bccg_sat_pullback
    (originalCnf : Prop) (closedCnf : Prop)
    (closedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bccg_ReconstructionWitnesses
      closedCnf originalCnf closedModel originalModel certificate conflict ->
    ay_bccg_Sat closedCnf closedModel ->
    ay_bccg_Sat originalCnf originalModel := by
  intro witnesses satClosed
  exact ay_bccg_model_reconstruction
    closedCnf originalCnf closedModel originalModel
    certificate conflict witnesses satClosed

theorem ay_bccg_unsat_pushback
    (originalCnf : Prop) (closedCnf : Prop)
    (closedModel : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) :
    ay_bccg_ReconstructionWitnesses
      closedCnf originalCnf closedModel originalModel certificate conflict ->
    ay_bccg_Replay closedCnf certificate conflict ->
    certificate -> originalCnf -> conflict := by
  intro witnesses replay
  exact ay_bccg_unsat_proof_reconstruction
    closedCnf originalCnf closedModel originalModel
    certificate conflict witnesses replay

theorem ay_bccg_public_sat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_bccg_ExitCodeSound exitCode (ay_bccg_Sat originalCnf originalModel) ->
    ay_bccg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro satSound
  exact ay_bccg_disj_left
    (ay_bccg_ExitCodeSound exitCode (ay_bccg_Sat originalCnf originalModel))
    (ay_bccg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    satSound

theorem ay_bccg_public_unsat_sound
    (originalCnf : Prop) (originalModel : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_bccg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_bccg_PublicResult originalCnf originalModel certificate conflict exitCode := by
  intro unsatSound
  exact ay_bccg_disj_right
    (ay_bccg_ExitCodeSound exitCode (ay_bccg_Sat originalCnf originalModel))
    (ay_bccg_ExitCodeSound exitCode
      (certificate -> originalCnf -> conflict))
    unsatSound

theorem ay_bccg_failure_digest
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    digestMismatch ->
    ay_bccg_BinaryClauseClosureGuardFailure
      digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result digest_case _graph_case _edge_case _implied_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact digest_case h

theorem ay_bccg_failure_graph
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    graphMismatch ->
    ay_bccg_BinaryClauseClosureGuardFailure
      digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case graph_case _edge_case _implied_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact graph_case h

theorem ay_bccg_failure_edge
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    edgeMismatch ->
    ay_bccg_BinaryClauseClosureGuardFailure
      digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _graph_case edge_case _implied_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact edge_case h

theorem ay_bccg_failure_implied
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    impliedMismatch ->
    ay_bccg_BinaryClauseClosureGuardFailure
      digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _graph_case _edge_case implied_case
    _reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact implied_case h

theorem ay_bccg_failure_reconstruction
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    reconstructionMismatch ->
    ay_bccg_BinaryClauseClosureGuardFailure
      digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _graph_case _edge_case _implied_case
    reconstruction_case _baseline_case _build_case _validator_case _audit_case
  exact reconstruction_case h

theorem ay_bccg_failure_baseline
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    baselineMismatch ->
    ay_bccg_BinaryClauseClosureGuardFailure
      digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _graph_case _edge_case _implied_case
    _reconstruction_case baseline_case _build_case _validator_case _audit_case
  exact baseline_case h

theorem ay_bccg_failure_build
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    buildMismatch ->
    ay_bccg_BinaryClauseClosureGuardFailure
      digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _graph_case _edge_case _implied_case
    _reconstruction_case _baseline_case build_case _validator_case _audit_case
  exact build_case h

theorem ay_bccg_failure_validator
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    validatorMismatch ->
    ay_bccg_BinaryClauseClosureGuardFailure
      digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _graph_case _edge_case _implied_case
    _reconstruction_case _baseline_case _build_case validator_case _audit_case
  exact validator_case h

theorem ay_bccg_failure_audit
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop) :
    auditMismatch ->
    ay_bccg_BinaryClauseClosureGuardFailure
      digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch := by
  intro h result _digest_case _graph_case _edge_case _implied_case
    _reconstruction_case _baseline_case _build_case _validator_case audit_case
  exact audit_case h

theorem ay_bccg_diagnostic_no_claim
    (currentCnf : Prop)
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bccg_DiagnosticBinaryClauseClosureGuard
      currentCnf digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_bccg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard
  exact ay_bccg_conj_right
    (ay_bccg_RecomputeObligation currentCnf recompute)
    (ay_bccg_NoSemanticClaim diagnostic)
    (ay_bccg_conj_right
      (ay_bccg_BinaryClauseClosureGuardFailure
        digestMismatch graphMismatch edgeMismatch impliedMismatch
        reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
        auditMismatch)
      (ay_bccg_Conj
        (ay_bccg_RecomputeObligation currentCnf recompute)
        (ay_bccg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_bccg_diagnostic_recompute
    (currentCnf : Prop)
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop) :
    ay_bccg_DiagnosticBinaryClauseClosureGuard
      currentCnf digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_bccg_RecomputeObligation currentCnf recompute := by
  intro diagnosticGuard
  exact ay_bccg_conj_left
    (ay_bccg_RecomputeObligation currentCnf recompute)
    (ay_bccg_NoSemanticClaim diagnostic)
    (ay_bccg_conj_right
      (ay_bccg_BinaryClauseClosureGuardFailure
        digestMismatch graphMismatch edgeMismatch impliedMismatch
        reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
        auditMismatch)
      (ay_bccg_Conj
        (ay_bccg_RecomputeObligation currentCnf recompute)
        (ay_bccg_NoSemanticClaim diagnostic))
      diagnosticGuard)

theorem ay_bccg_failed_closure_cannot_bless_public_result
    (currentCnf : Prop)
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop)
    (certificate : Prop) (conflict : Prop) (exitCode : Prop) :
    ay_bccg_DiagnosticBinaryClauseClosureGuard
      currentCnf digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_bccg_PublicResult originalCnf model certificate conflict exitCode ->
    ay_bccg_Conj
      (ay_bccg_NoSemanticClaim diagnostic)
      (ay_bccg_RecomputeObligation currentCnf recompute) := by
  intro diagnosticGuard _publicResult
  exact ay_bccg_conj_intro
    (ay_bccg_NoSemanticClaim diagnostic)
    (ay_bccg_RecomputeObligation currentCnf recompute)
    (ay_bccg_diagnostic_no_claim
      currentCnf digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic diagnosticGuard)
    (ay_bccg_diagnostic_recompute
      currentCnf digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic diagnosticGuard)

theorem ay_bccg_failed_closure_cannot_bless_public_sat
    (currentCnf : Prop)
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (model : Prop) (exitCode : Prop) :
    ay_bccg_DiagnosticBinaryClauseClosureGuard
      currentCnf digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_bccg_ExitCodeSound exitCode (ay_bccg_Sat originalCnf model) ->
    ay_bccg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _satClaim
  exact ay_bccg_diagnostic_no_claim
    currentCnf digestMismatch graphMismatch edgeMismatch impliedMismatch
    reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
    auditMismatch recompute diagnostic diagnosticGuard

theorem ay_bccg_failed_closure_cannot_bless_public_unsat
    (currentCnf : Prop)
    (digestMismatch graphMismatch edgeMismatch impliedMismatch : Prop)
    (reconstructionMismatch baselineMismatch buildMismatch validatorMismatch : Prop)
    (auditMismatch : Prop)
    (recompute : Prop) (diagnostic : Prop)
    (originalCnf : Prop) (certificate : Prop) (conflict : Prop)
    (exitCode : Prop) :
    ay_bccg_DiagnosticBinaryClauseClosureGuard
      currentCnf digestMismatch graphMismatch edgeMismatch impliedMismatch
      reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
      auditMismatch recompute diagnostic ->
    ay_bccg_ExitCodeSound exitCode (certificate -> originalCnf -> conflict) ->
    ay_bccg_NoSemanticClaim diagnostic := by
  intro diagnosticGuard _unsatClaim
  exact ay_bccg_diagnostic_no_claim
    currentCnf digestMismatch graphMismatch edgeMismatch impliedMismatch
    reconstructionMismatch baselineMismatch buildMismatch validatorMismatch
    auditMismatch recompute diagnostic diagnosticGuard
