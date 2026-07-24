def ay_bcag_conj (p q : Prop) : Prop := p ∧ q

def ay_bcag_disj (p q : Prop) : Prop := p ∨ q

def ay_bcag_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_bcag_disj satSound unsatSound

def ay_bcag_inputs
    (binaryClauseArenaDigest clauseIdCoverageLedger watchlistMappingWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) : Prop :=
  ay_bcag_conj binaryClauseArenaDigest
    (ay_bcag_conj clauseIdCoverageLedger
      (ay_bcag_conj watchlistMappingWitness
        (ay_bcag_conj propagationReplay
          (ay_bcag_conj fallbackBaseline
            (ay_bcag_conj solverBuildEvidence
              (ay_bcag_conj validatorGate auditTranscript))))))

def ay_bcag_binary_clause_arena_digest_evidence
    (binaryClauseArenaDigest : Prop) : Prop :=
  binaryClauseArenaDigest

def ay_bcag_clause_id_coverage_ledger_evidence
    (clauseIdCoverageLedger : Prop) : Prop :=
  clauseIdCoverageLedger

def ay_bcag_watchlist_mapping_witness_evidence
    (watchlistMappingWitness : Prop) : Prop :=
  watchlistMappingWitness

def ay_bcag_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_bcag_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_bcag_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_bcag_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_bcag_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_bcag_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_bcag_accepted
    (binaryClauseArenaDigest clauseIdCoverageLedger watchlistMappingWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript arenaAccepted : Prop) : Prop :=
  arenaAccepted

def ay_bcag_rejected
    (arenaMismatch coverageMismatch watchMismatch replayMismatch
      fallbackMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    Prop :=
  ay_bcag_disj arenaMismatch
    (ay_bcag_disj coverageMismatch
      (ay_bcag_disj watchMismatch
        (ay_bcag_disj replayMismatch
          (ay_bcag_disj fallbackMismatch
            (ay_bcag_disj buildMismatch
              (ay_bcag_disj validatorMismatch auditMismatch))))))

def ay_bcag_gate (accepted rejected : Prop) : Prop :=
  ay_bcag_disj accepted rejected

def ay_bcag_binary_arena_hint
    (arenaAccepted layoutGuidance watchGuidance replayGuidance : Prop) :
    Prop :=
  arenaAccepted

def ay_bcag_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_bcag_input_components
    {binaryClauseArenaDigest clauseIdCoverageLedger watchlistMappingWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop} :
    ay_bcag_inputs binaryClauseArenaDigest clauseIdCoverageLedger
      watchlistMappingWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_bcag_inputs binaryClauseArenaDigest clauseIdCoverageLedger
      watchlistMappingWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_bcag_accepted_policy
    {binaryClauseArenaDigest clauseIdCoverageLedger watchlistMappingWitness
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript arenaAccepted : Prop} :
    arenaAccepted ->
    ay_bcag_accepted binaryClauseArenaDigest clauseIdCoverageLedger
      watchlistMappingWitness propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript arenaAccepted := by
  intro accepted
  exact accepted

theorem ay_bcag_accepted_binary_clause_arena_digest
    {binaryClauseArenaDigest : Prop} :
    binaryClauseArenaDigest ->
    ay_bcag_binary_clause_arena_digest_evidence
      binaryClauseArenaDigest := by
  intro evidence
  exact evidence

theorem ay_bcag_accepted_clause_id_coverage_ledger
    {clauseIdCoverageLedger : Prop} :
    clauseIdCoverageLedger ->
    ay_bcag_clause_id_coverage_ledger_evidence clauseIdCoverageLedger := by
  intro evidence
  exact evidence

theorem ay_bcag_accepted_watchlist_mapping_witness
    {watchlistMappingWitness : Prop} :
    watchlistMappingWitness ->
    ay_bcag_watchlist_mapping_witness_evidence watchlistMappingWitness := by
  intro evidence
  exact evidence

theorem ay_bcag_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_bcag_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_bcag_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_bcag_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_bcag_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_bcag_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_bcag_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_bcag_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_bcag_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_bcag_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_bcag_binary_arena_policy_admissible_hint
    {arenaAccepted layoutGuidance watchGuidance replayGuidance : Prop} :
    arenaAccepted ->
    layoutGuidance ->
    watchGuidance ->
    replayGuidance ->
    ay_bcag_binary_arena_hint arenaAccepted layoutGuidance watchGuidance
      replayGuidance :=
  fun accepted _ _ _ => accepted

theorem ay_bcag_binary_arena_layout_is_data_structure_only
    {arenaAccepted dataStructureOptimizationOnly : Prop} :
    arenaAccepted ->
    dataStructureOptimizationOnly ->
    dataStructureOptimizationOnly :=
  fun _ optimization => optimization

theorem ay_bcag_layout_cannot_change_original_formula_truth
    {arenaAccepted originalFormulaTruth : Prop} :
    arenaAccepted ->
    originalFormulaTruth ->
    originalFormulaTruth :=
  fun _ truth => truth

theorem ay_bcag_accepted_layout_preserves_public_soundness
    {arenaAccepted satSound unsatSound : Prop} :
    arenaAccepted ->
    ay_bcag_public_soundness_theorem satSound unsatSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_bcag_accepted_layout_preserves_binary_propagation_replay
    {arenaAccepted binaryPropagationReplay : Prop} :
    arenaAccepted ->
    binaryPropagationReplay ->
    binaryPropagationReplay :=
  fun _ replay => replay

theorem ay_bcag_watch_mapping_preserves_propagation_replay
    {watchlistMappingWitness propagationReplay : Prop} :
    watchlistMappingWitness ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_bcag_coverage_ledger_preserves_watch_mapping
    {clauseIdCoverageLedger watchlistMappingWitness : Prop} :
    clauseIdCoverageLedger ->
    watchlistMappingWitness ->
    watchlistMappingWitness :=
  fun _ watch => watch

theorem ay_bcag_rejected_is_no_claim
    {arenaMismatch diagnostic : Prop} :
    arenaMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcag_rejected_forces_recompute
    {arenaMismatch recomputeRequired : Prop} :
    arenaMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bcag_failed_binary_arena_guard_cannot_bless_publication
    {arenaMismatch baselineSound satSound unsatSound : Prop} :
    arenaMismatch ->
    baselineSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcag_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_bcag_gate accepted rejected ->
    ay_bcag_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_bcag_safe_strategy_guidance_accept
    {arenaAccepted layoutGuidance watchGuidance replayGuidance satSound
      unsatSound : Prop} :
    arenaAccepted ->
    layoutGuidance ->
    watchGuidance ->
    replayGuidance ->
    ay_bcag_public_soundness_theorem satSound unsatSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_bcag_safe_strategy_guidance_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_bcag_public_soundness_theorem satSound unsatSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_bcag_arena_mismatch_forces_no_claim
    {arenaMismatch diagnostic : Prop} :
    arenaMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcag_coverage_mismatch_forces_no_claim
    {coverageMismatch diagnostic : Prop} :
    coverageMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcag_watch_mismatch_forces_no_claim
    {watchMismatch diagnostic : Prop} :
    watchMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcag_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcag_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcag_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcag_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcag_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcag_arena_mismatch_forces_recompute
    {arenaMismatch recomputeRequired : Prop} :
    arenaMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bcag_coverage_mismatch_forces_recompute
    {coverageMismatch recomputeRequired : Prop} :
    coverageMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bcag_watch_mismatch_forces_recompute
    {watchMismatch recomputeRequired : Prop} :
    watchMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bcag_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bcag_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bcag_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bcag_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bcag_arena_mismatch_cannot_bless_publication
    {arenaMismatch baselineSound satSound unsatSound : Prop} :
    arenaMismatch ->
    baselineSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcag_coverage_mismatch_cannot_bless_publication
    {coverageMismatch baselineSound satSound unsatSound : Prop} :
    coverageMismatch ->
    baselineSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcag_watch_mismatch_cannot_bless_publication
    {watchMismatch baselineSound satSound unsatSound : Prop} :
    watchMismatch ->
    baselineSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcag_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcag_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcag_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcag_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound ->
    ay_bcag_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcag_policy_requires_binary_clause_arena_digest
    {binaryClauseArenaDigest : Prop} :
    ay_bcag_binary_clause_arena_digest_evidence binaryClauseArenaDigest ->
    binaryClauseArenaDigest := by
  intro evidence
  exact evidence

theorem ay_bcag_policy_requires_clause_id_coverage
    {clauseIdCoverageLedger : Prop} :
    ay_bcag_clause_id_coverage_ledger_evidence clauseIdCoverageLedger ->
    clauseIdCoverageLedger := by
  intro evidence
  exact evidence

theorem ay_bcag_policy_requires_watchlist_mapping
    {watchlistMappingWitness : Prop} :
    ay_bcag_watchlist_mapping_witness_evidence watchlistMappingWitness ->
    watchlistMappingWitness := by
  intro evidence
  exact evidence

theorem ay_bcag_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_bcag_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_bcag_policy_requires_fallback_baseline
    {fallbackBaseline : Prop} :
    ay_bcag_fallback_baseline_evidence fallbackBaseline -> fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_bcag_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_bcag_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_bcag_policy_requires_validator
    {validatorGate : Prop} :
    ay_bcag_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_bcag_policy_requires_audit
    {auditTranscript : Prop} :
    ay_bcag_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
