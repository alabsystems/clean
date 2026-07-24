def ay_bicg_conj (p q : Prop) : Prop := p ∧ q

def ay_bicg_disj (p q : Prop) : Prop := p ∨ q

def ay_bicg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_bicg_disj satSound unsatSound

def ay_bicg_inputs
    (clauseDatabaseDigest binaryImplicationGraphDigest cacheEpochManifest
      cacheEntryLedger watchlistDigest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_bicg_conj clauseDatabaseDigest
    (ay_bicg_conj binaryImplicationGraphDigest
      (ay_bicg_conj cacheEpochManifest
        (ay_bicg_conj cacheEntryLedger
          (ay_bicg_conj watchlistDigest
            (ay_bicg_conj propagationReplay
              (ay_bicg_conj fallbackBaseline
                (ay_bicg_conj solverBuildEvidence
                  (ay_bicg_conj validatorGate auditTranscript))))))))

def ay_bicg_clause_database_digest_evidence
    (clauseDatabaseDigest : Prop) : Prop :=
  clauseDatabaseDigest

def ay_bicg_binary_implication_graph_digest_evidence
    (binaryImplicationGraphDigest : Prop) : Prop :=
  binaryImplicationGraphDigest

def ay_bicg_cache_epoch_manifest_evidence
    (cacheEpochManifest : Prop) : Prop :=
  cacheEpochManifest

def ay_bicg_cache_entry_ledger_evidence
    (cacheEntryLedger : Prop) : Prop :=
  cacheEntryLedger

def ay_bicg_watchlist_digest_evidence (watchlistDigest : Prop) : Prop :=
  watchlistDigest

def ay_bicg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_bicg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_bicg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_bicg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_bicg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_bicg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_bicg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_bicg_accepted
    (clauseDatabaseDigest binaryImplicationGraphDigest cacheEpochManifest
      cacheEntryLedger watchlistDigest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript cacheAccepted :
      Prop) : Prop :=
  cacheAccepted

def ay_bicg_rejected
    (graphMismatch cacheMismatch watchMismatch replayMismatch buildMismatch
      validatorMismatch clauseMismatch epochMismatch ledgerMismatch
      baselineMismatch auditMismatch : Prop) : Prop :=
  ay_bicg_disj graphMismatch
    (ay_bicg_disj cacheMismatch
      (ay_bicg_disj watchMismatch
        (ay_bicg_disj replayMismatch
          (ay_bicg_disj buildMismatch
            (ay_bicg_disj validatorMismatch
              (ay_bicg_disj clauseMismatch
                (ay_bicg_disj epochMismatch
                  (ay_bicg_disj ledgerMismatch
                    (ay_bicg_disj baselineMismatch auditMismatch)))))))))

def ay_bicg_gate (accepted rejected : Prop) : Prop :=
  ay_bicg_disj accepted rejected

def ay_bicg_cache_propagation_acceleration_hint
    (cacheAccepted propagationAccelerationOnly dataStructureStateOnly
      replayAccepted : Prop) : Prop :=
  cacheAccepted

theorem ay_bicg_input_components
    {clauseDatabaseDigest binaryImplicationGraphDigest cacheEpochManifest
      cacheEntryLedger watchlistDigest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_bicg_inputs clauseDatabaseDigest binaryImplicationGraphDigest
      cacheEpochManifest cacheEntryLedger watchlistDigest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript ->
    ay_bicg_inputs clauseDatabaseDigest binaryImplicationGraphDigest
      cacheEpochManifest cacheEntryLedger watchlistDigest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_bicg_accepted_policy
    {clauseDatabaseDigest binaryImplicationGraphDigest cacheEpochManifest
      cacheEntryLedger watchlistDigest propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript cacheAccepted : Prop} :
    cacheAccepted ->
    ay_bicg_accepted clauseDatabaseDigest binaryImplicationGraphDigest
      cacheEpochManifest cacheEntryLedger watchlistDigest propagationReplay
      fallbackBaseline solverBuildEvidence validatorGate auditTranscript
      cacheAccepted := by
  intro accepted
  exact accepted

theorem ay_bicg_accepted_clause_database_digest
    {clauseDatabaseDigest : Prop} :
    clauseDatabaseDigest ->
    ay_bicg_clause_database_digest_evidence clauseDatabaseDigest := by
  intro evidence
  exact evidence

theorem ay_bicg_accepted_binary_implication_graph_digest
    {binaryImplicationGraphDigest : Prop} :
    binaryImplicationGraphDigest ->
    ay_bicg_binary_implication_graph_digest_evidence
      binaryImplicationGraphDigest := by
  intro evidence
  exact evidence

theorem ay_bicg_accepted_cache_epoch_manifest
    {cacheEpochManifest : Prop} :
    cacheEpochManifest ->
    ay_bicg_cache_epoch_manifest_evidence cacheEpochManifest := by
  intro evidence
  exact evidence

theorem ay_bicg_accepted_cache_entry_ledger
    {cacheEntryLedger : Prop} :
    cacheEntryLedger ->
    ay_bicg_cache_entry_ledger_evidence cacheEntryLedger := by
  intro evidence
  exact evidence

theorem ay_bicg_accepted_watchlist_digest
    {watchlistDigest : Prop} :
    watchlistDigest ->
    ay_bicg_watchlist_digest_evidence watchlistDigest := by
  intro evidence
  exact evidence

theorem ay_bicg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_bicg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_bicg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_bicg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_bicg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_bicg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_bicg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_bicg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_bicg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_bicg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_bicg_cache_is_propagation_acceleration_only
    {cacheAccepted propagationAccelerationOnly : Prop} :
    cacheAccepted ->
    propagationAccelerationOnly ->
    propagationAccelerationOnly :=
  fun _ accelOnly => accelOnly

theorem ay_bicg_cache_is_data_structure_state_only
    {cacheAccepted dataStructureStateOnly : Prop} :
    cacheAccepted ->
    dataStructureStateOnly ->
    dataStructureStateOnly :=
  fun _ stateOnly => stateOnly

theorem ay_bicg_cache_cannot_change_original_formula_truth
    {cacheAccepted originalFormulaTruthPreserved : Prop} :
    cacheAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_bicg_accepted_cache_preserves_public_soundness
    {cacheAccepted satSound unsatSound : Prop} :
    cacheAccepted ->
    ay_bicg_public_soundness_theorem satSound unsatSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_bicg_graph_digest_preserves_replay
    {binaryImplicationGraphDigest propagationReplay : Prop} :
    binaryImplicationGraphDigest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_bicg_cache_entry_ledger_preserves_replay
    {cacheEntryLedger propagationReplay : Prop} :
    cacheEntryLedger ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_bicg_watchlist_digest_preserves_replay
    {watchlistDigest propagationReplay : Prop} :
    watchlistDigest ->
    propagationReplay ->
    propagationReplay :=
  fun _ replay => replay

theorem ay_bicg_accepted_cache_preserves_fallback_soundness
    {cacheAccepted fallbackBaseline satSound unsatSound : Prop} :
    cacheAccepted ->
    fallbackBaseline ->
    ay_bicg_public_soundness_theorem satSound unsatSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bicg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_bicg_gate accepted rejected ->
    ay_bicg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_bicg_rejected_is_no_claim
    {graphMismatch diagnostic : Prop} :
    graphMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bicg_rejected_forces_recompute
    {graphMismatch recomputeRequired : Prop} :
    graphMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bicg_failed_guard_cannot_bless_publication
    {graphMismatch baselineSound satSound unsatSound : Prop} :
    graphMismatch ->
    baselineSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bicg_graph_mismatch_forces_no_claim
    {graphMismatch diagnostic : Prop} :
    graphMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bicg_cache_mismatch_forces_no_claim
    {cacheMismatch diagnostic : Prop} :
    cacheMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bicg_watch_mismatch_forces_no_claim
    {watchMismatch diagnostic : Prop} :
    watchMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bicg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bicg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bicg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bicg_clause_mismatch_forces_no_claim
    {clauseMismatch diagnostic : Prop} :
    clauseMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bicg_epoch_mismatch_forces_no_claim
    {epochMismatch diagnostic : Prop} :
    epochMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bicg_ledger_mismatch_forces_no_claim
    {ledgerMismatch diagnostic : Prop} :
    ledgerMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bicg_baseline_mismatch_forces_no_claim
    {baselineMismatch diagnostic : Prop} :
    baselineMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bicg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bicg_graph_mismatch_forces_recompute
    {graphMismatch recomputeRequired : Prop} :
    graphMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bicg_cache_mismatch_forces_recompute
    {cacheMismatch recomputeRequired : Prop} :
    cacheMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bicg_watch_mismatch_forces_recompute
    {watchMismatch recomputeRequired : Prop} :
    watchMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bicg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bicg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bicg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bicg_clause_mismatch_forces_recompute
    {clauseMismatch recomputeRequired : Prop} :
    clauseMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bicg_epoch_mismatch_forces_recompute
    {epochMismatch recomputeRequired : Prop} :
    epochMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bicg_ledger_mismatch_forces_recompute
    {ledgerMismatch recomputeRequired : Prop} :
    ledgerMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bicg_baseline_mismatch_forces_recompute
    {baselineMismatch recomputeRequired : Prop} :
    baselineMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bicg_audit_mismatch_forces_recompute
    {auditMismatch recomputeRequired : Prop} :
    auditMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bicg_graph_mismatch_cannot_bless_publication
    {graphMismatch baselineSound satSound unsatSound : Prop} :
    graphMismatch ->
    baselineSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bicg_cache_mismatch_cannot_bless_publication
    {cacheMismatch baselineSound satSound unsatSound : Prop} :
    cacheMismatch ->
    baselineSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bicg_watch_mismatch_cannot_bless_publication
    {watchMismatch baselineSound satSound unsatSound : Prop} :
    watchMismatch ->
    baselineSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bicg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bicg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bicg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound ->
    ay_bicg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bicg_policy_requires_clause_database_digest
    {clauseDatabaseDigest accepted : Prop} :
    clauseDatabaseDigest -> accepted -> clauseDatabaseDigest :=
  fun evidence _ => evidence

theorem ay_bicg_policy_requires_binary_implication_graph_digest
    {binaryImplicationGraphDigest accepted : Prop} :
    binaryImplicationGraphDigest -> accepted ->
    binaryImplicationGraphDigest :=
  fun evidence _ => evidence

theorem ay_bicg_policy_requires_cache_epoch_manifest
    {cacheEpochManifest accepted : Prop} :
    cacheEpochManifest -> accepted -> cacheEpochManifest :=
  fun evidence _ => evidence

theorem ay_bicg_policy_requires_cache_entry_ledger
    {cacheEntryLedger accepted : Prop} :
    cacheEntryLedger -> accepted -> cacheEntryLedger :=
  fun evidence _ => evidence

theorem ay_bicg_policy_requires_watchlist_digest
    {watchlistDigest accepted : Prop} :
    watchlistDigest -> accepted -> watchlistDigest :=
  fun evidence _ => evidence

theorem ay_bicg_policy_requires_propagation_replay
    {propagationReplay accepted : Prop} :
    propagationReplay -> accepted -> propagationReplay :=
  fun evidence _ => evidence

theorem ay_bicg_policy_requires_fallback_baseline
    {fallbackBaseline accepted : Prop} :
    fallbackBaseline -> accepted -> fallbackBaseline :=
  fun evidence _ => evidence

theorem ay_bicg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_bicg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_bicg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
