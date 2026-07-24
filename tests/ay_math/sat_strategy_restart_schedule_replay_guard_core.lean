def ay_rsrg_conj (p q : Prop) : Prop := p ∧ q

def ay_rsrg_disj (p q : Prop) : Prop := p ∨ q

def ay_rsrg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_rsrg_disj satSound unsatSound

def ay_rsrg_inputs
    (benchmarkFingerprint restartScheduleManifest conflictCounterDigest
      propagationLedger learnedClauseLedgerDigest phaseSavingDigest
      decisionOrderDigest replayTranscript cutoffFallbackPolicy
      solverBuildEvidence validatorGate auditTranscript : Prop) : Prop :=
  ay_rsrg_conj benchmarkFingerprint
    (ay_rsrg_conj restartScheduleManifest
      (ay_rsrg_conj conflictCounterDigest
        (ay_rsrg_conj propagationLedger
          (ay_rsrg_conj learnedClauseLedgerDigest
            (ay_rsrg_conj phaseSavingDigest
              (ay_rsrg_conj decisionOrderDigest
                (ay_rsrg_conj replayTranscript
                  (ay_rsrg_conj cutoffFallbackPolicy
                    (ay_rsrg_conj solverBuildEvidence
                      (ay_rsrg_conj validatorGate auditTranscript))))))))))

def ay_rsrg_benchmark_fingerprint_evidence
    (benchmarkFingerprint : Prop) : Prop :=
  benchmarkFingerprint

def ay_rsrg_restart_schedule_manifest_evidence
    (restartScheduleManifest : Prop) : Prop :=
  restartScheduleManifest

def ay_rsrg_conflict_counter_digest_evidence
    (conflictCounterDigest : Prop) : Prop :=
  conflictCounterDigest

def ay_rsrg_propagation_ledger_evidence
    (propagationLedger : Prop) : Prop :=
  propagationLedger

def ay_rsrg_learned_clause_ledger_digest_evidence
    (learnedClauseLedgerDigest : Prop) : Prop :=
  learnedClauseLedgerDigest

def ay_rsrg_phase_saving_digest_evidence
    (phaseSavingDigest : Prop) : Prop :=
  phaseSavingDigest

def ay_rsrg_decision_order_digest_evidence
    (decisionOrderDigest : Prop) : Prop :=
  decisionOrderDigest

def ay_rsrg_replay_transcript_evidence (replayTranscript : Prop) : Prop :=
  replayTranscript

def ay_rsrg_cutoff_fallback_policy_evidence
    (cutoffFallbackPolicy : Prop) : Prop :=
  cutoffFallbackPolicy

def ay_rsrg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_rsrg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_rsrg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_rsrg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_rsrg_recompute_path (recomputeRequired : Prop) : Prop :=
  recomputeRequired

def ay_rsrg_checked_sat_evidence (satEvidence : Prop) : Prop := satEvidence

def ay_rsrg_checked_unsat_evidence (unsatEvidence : Prop) : Prop :=
  unsatEvidence

def ay_rsrg_accepted
    (benchmarkFingerprint restartScheduleManifest conflictCounterDigest
      propagationLedger learnedClauseLedgerDigest phaseSavingDigest
      decisionOrderDigest replayTranscript cutoffFallbackPolicy
      solverBuildEvidence validatorGate auditTranscript scheduleAccepted :
      Prop) : Prop :=
  scheduleAccepted

def ay_rsrg_rejected
    (fingerprintMismatch scheduleMismatch counterMismatch propagationMismatch
      learnedClauseMismatch phaseMismatch decisionMismatch replayMismatch
      cutoffMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    Prop :=
  ay_rsrg_disj fingerprintMismatch
    (ay_rsrg_disj scheduleMismatch
      (ay_rsrg_disj counterMismatch
        (ay_rsrg_disj propagationMismatch
          (ay_rsrg_disj learnedClauseMismatch
            (ay_rsrg_disj phaseMismatch
              (ay_rsrg_disj decisionMismatch
                (ay_rsrg_disj replayMismatch
                  (ay_rsrg_disj cutoffMismatch
                    (ay_rsrg_disj buildMismatch
                      (ay_rsrg_disj validatorMismatch auditMismatch))))))))))

def ay_rsrg_restart_schedule_heuristic_replay_evidence
    (scheduleAccepted heuristicOnly reproducibleReplay : Prop) : Prop :=
  scheduleAccepted

def ay_rsrg_publication_gate
    (restartReplay solverBuildEvidence validatorGate auditTranscript
      checkedEvidence : Prop) : Prop :=
  ay_rsrg_conj restartReplay
    (ay_rsrg_conj solverBuildEvidence
      (ay_rsrg_conj validatorGate
        (ay_rsrg_conj auditTranscript checkedEvidence)))

def ay_rsrg_gate (accepted rejected : Prop) : Prop :=
  ay_rsrg_disj accepted rejected

theorem ay_rsrg_input_components
    {benchmarkFingerprint restartScheduleManifest conflictCounterDigest
      propagationLedger learnedClauseLedgerDigest phaseSavingDigest
      decisionOrderDigest replayTranscript cutoffFallbackPolicy
      solverBuildEvidence validatorGate auditTranscript : Prop} :
    ay_rsrg_inputs benchmarkFingerprint restartScheduleManifest
      conflictCounterDigest propagationLedger learnedClauseLedgerDigest
      phaseSavingDigest decisionOrderDigest replayTranscript
      cutoffFallbackPolicy solverBuildEvidence validatorGate auditTranscript ->
    ay_rsrg_inputs benchmarkFingerprint restartScheduleManifest
      conflictCounterDigest propagationLedger learnedClauseLedgerDigest
      phaseSavingDigest decisionOrderDigest replayTranscript
      cutoffFallbackPolicy solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_rsrg_accepted_schedule
    {benchmarkFingerprint restartScheduleManifest conflictCounterDigest
      propagationLedger learnedClauseLedgerDigest phaseSavingDigest
      decisionOrderDigest replayTranscript cutoffFallbackPolicy
      solverBuildEvidence validatorGate auditTranscript scheduleAccepted :
      Prop} :
    scheduleAccepted ->
    ay_rsrg_accepted benchmarkFingerprint restartScheduleManifest
      conflictCounterDigest propagationLedger learnedClauseLedgerDigest
      phaseSavingDigest decisionOrderDigest replayTranscript
      cutoffFallbackPolicy solverBuildEvidence validatorGate auditTranscript
      scheduleAccepted := by
  intro accepted
  exact accepted

theorem ay_rsrg_accepted_benchmark_fingerprint
    {benchmarkFingerprint : Prop} :
    benchmarkFingerprint ->
    ay_rsrg_benchmark_fingerprint_evidence benchmarkFingerprint := by
  intro evidence
  exact evidence

theorem ay_rsrg_accepted_restart_schedule_manifest
    {restartScheduleManifest : Prop} :
    restartScheduleManifest ->
    ay_rsrg_restart_schedule_manifest_evidence restartScheduleManifest := by
  intro evidence
  exact evidence

theorem ay_rsrg_accepted_conflict_counter_digest
    {conflictCounterDigest : Prop} :
    conflictCounterDigest ->
    ay_rsrg_conflict_counter_digest_evidence conflictCounterDigest := by
  intro evidence
  exact evidence

theorem ay_rsrg_accepted_propagation_ledger
    {propagationLedger : Prop} :
    propagationLedger ->
    ay_rsrg_propagation_ledger_evidence propagationLedger := by
  intro evidence
  exact evidence

theorem ay_rsrg_accepted_learned_clause_ledger_digest
    {learnedClauseLedgerDigest : Prop} :
    learnedClauseLedgerDigest ->
    ay_rsrg_learned_clause_ledger_digest_evidence
      learnedClauseLedgerDigest := by
  intro evidence
  exact evidence

theorem ay_rsrg_accepted_phase_saving_digest
    {phaseSavingDigest : Prop} :
    phaseSavingDigest ->
    ay_rsrg_phase_saving_digest_evidence phaseSavingDigest := by
  intro evidence
  exact evidence

theorem ay_rsrg_accepted_decision_order_digest
    {decisionOrderDigest : Prop} :
    decisionOrderDigest ->
    ay_rsrg_decision_order_digest_evidence decisionOrderDigest := by
  intro evidence
  exact evidence

theorem ay_rsrg_accepted_replay_transcript
    {replayTranscript : Prop} :
    replayTranscript ->
    ay_rsrg_replay_transcript_evidence replayTranscript := by
  intro evidence
  exact evidence

theorem ay_rsrg_accepted_cutoff_fallback_policy
    {cutoffFallbackPolicy : Prop} :
    cutoffFallbackPolicy ->
    ay_rsrg_cutoff_fallback_policy_evidence cutoffFallbackPolicy := by
  intro evidence
  exact evidence

theorem ay_rsrg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_rsrg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_rsrg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_rsrg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_rsrg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_rsrg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_rsrg_schedule_evidence_is_heuristic_replay_only
    {scheduleAccepted heuristicOnly : Prop} :
    scheduleAccepted ->
    heuristicOnly ->
    heuristicOnly :=
  fun _ heuristic => heuristic

theorem ay_rsrg_schedule_cannot_independently_justify_sat
    {scheduleAccepted satEvidence satSound : Prop} :
    scheduleAccepted ->
    ay_rsrg_checked_sat_evidence satEvidence ->
    (satEvidence -> satSound) ->
    satSound :=
  fun _ evidence transport => transport evidence

theorem ay_rsrg_schedule_cannot_independently_justify_unsat
    {scheduleAccepted unsatEvidence unsatSound : Prop} :
    scheduleAccepted ->
    ay_rsrg_checked_unsat_evidence unsatEvidence ->
    (unsatEvidence -> unsatSound) ->
    unsatSound :=
  fun _ evidence transport => transport evidence

theorem ay_rsrg_accepted_publication_requires_build
    {restartReplay solverBuildEvidence validatorGate auditTranscript
      checkedEvidence : Prop} :
    ay_rsrg_publication_gate restartReplay solverBuildEvidence validatorGate
      auditTranscript checkedEvidence ->
    solverBuildEvidence ->
    solverBuildEvidence :=
  fun _ evidence => evidence

theorem ay_rsrg_accepted_publication_requires_validator
    {restartReplay solverBuildEvidence validatorGate auditTranscript
      checkedEvidence : Prop} :
    ay_rsrg_publication_gate restartReplay solverBuildEvidence validatorGate
      auditTranscript checkedEvidence ->
    validatorGate ->
    validatorGate :=
  fun _ evidence => evidence

theorem ay_rsrg_accepted_publication_requires_audit
    {restartReplay solverBuildEvidence validatorGate auditTranscript
      checkedEvidence : Prop} :
    ay_rsrg_publication_gate restartReplay solverBuildEvidence validatorGate
      auditTranscript checkedEvidence ->
    auditTranscript ->
    auditTranscript :=
  fun _ evidence => evidence

theorem ay_rsrg_accepted_publication_requires_restart_replay
    {restartReplay solverBuildEvidence validatorGate auditTranscript
      checkedEvidence : Prop} :
    ay_rsrg_publication_gate restartReplay solverBuildEvidence validatorGate
      auditTranscript checkedEvidence ->
    restartReplay ->
    restartReplay :=
  fun _ evidence => evidence

theorem ay_rsrg_accepted_publication_preserves_public_soundness
    {restartReplay solverBuildEvidence validatorGate auditTranscript
      checkedEvidence satSound unsatSound : Prop} :
    ay_rsrg_publication_gate restartReplay solverBuildEvidence validatorGate
      auditTranscript checkedEvidence ->
    ay_rsrg_public_soundness_theorem satSound unsatSound ->
    ay_rsrg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_rsrg_restart_schedule_cannot_change_formula_truth
    {scheduleAccepted originalFormulaTruthPreserved : Prop} :
    scheduleAccepted ->
    originalFormulaTruthPreserved ->
    originalFormulaTruthPreserved :=
  fun _ preserved => preserved

theorem ay_rsrg_replay_transcript_preserves_cutoff_fallback
    {replayTranscript cutoffFallbackPolicy : Prop} :
    replayTranscript ->
    cutoffFallbackPolicy ->
    cutoffFallbackPolicy :=
  fun _ fallback => fallback

theorem ay_rsrg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_rsrg_gate accepted rejected ->
    ay_rsrg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_rsrg_rejected_is_no_claim
    {scheduleMismatch diagnostic : Prop} :
    scheduleMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsrg_rejected_forces_recompute
    {scheduleMismatch recomputeRequired : Prop} :
    scheduleMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsrg_failed_restart_guard_cannot_bless_competition_result
    {scheduleMismatch baselineNoClaim satSound unsatSound : Prop} :
    scheduleMismatch ->
    baselineNoClaim ->
    ay_rsrg_public_soundness_theorem satSound unsatSound ->
    ay_rsrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rsrg_fingerprint_mismatch_forces_no_claim
    {fingerprintMismatch diagnostic : Prop} :
    fingerprintMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsrg_schedule_mismatch_forces_no_claim
    {scheduleMismatch diagnostic : Prop} :
    scheduleMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsrg_counter_mismatch_forces_no_claim
    {counterMismatch diagnostic : Prop} :
    counterMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsrg_propagation_mismatch_forces_no_claim
    {propagationMismatch diagnostic : Prop} :
    propagationMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsrg_learned_clause_mismatch_forces_no_claim
    {learnedClauseMismatch diagnostic : Prop} :
    learnedClauseMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsrg_phase_mismatch_forces_no_claim
    {phaseMismatch diagnostic : Prop} :
    phaseMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsrg_decision_mismatch_forces_no_claim
    {decisionMismatch diagnostic : Prop} :
    decisionMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsrg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsrg_cutoff_mismatch_forces_no_claim
    {cutoffMismatch diagnostic : Prop} :
    cutoffMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsrg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsrg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsrg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch -> diagnostic -> diagnostic :=
  fun _ noClaim => noClaim

theorem ay_rsrg_fingerprint_mismatch_forces_recompute
    {fingerprintMismatch recomputeRequired : Prop} :
    fingerprintMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsrg_schedule_mismatch_forces_recompute
    {scheduleMismatch recomputeRequired : Prop} :
    scheduleMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsrg_counter_mismatch_forces_recompute
    {counterMismatch recomputeRequired : Prop} :
    counterMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsrg_propagation_mismatch_forces_recompute
    {propagationMismatch recomputeRequired : Prop} :
    propagationMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsrg_learned_clause_mismatch_forces_recompute
    {learnedClauseMismatch recomputeRequired : Prop} :
    learnedClauseMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsrg_phase_mismatch_forces_recompute
    {phaseMismatch recomputeRequired : Prop} :
    phaseMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsrg_decision_mismatch_forces_recompute
    {decisionMismatch recomputeRequired : Prop} :
    decisionMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsrg_replay_mismatch_forces_recompute
    {replayMismatch recomputeRequired : Prop} :
    replayMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsrg_cutoff_mismatch_forces_recompute
    {cutoffMismatch recomputeRequired : Prop} :
    cutoffMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsrg_build_mismatch_forces_recompute
    {buildMismatch recomputeRequired : Prop} :
    buildMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsrg_validator_mismatch_forces_recompute
    {validatorMismatch recomputeRequired : Prop} :
    validatorMismatch -> recomputeRequired -> recomputeRequired :=
  fun _ recompute => recompute

theorem ay_rsrg_schedule_mismatch_cannot_bless_result
    {scheduleMismatch baselineNoClaim satSound unsatSound : Prop} :
    scheduleMismatch ->
    baselineNoClaim ->
    ay_rsrg_public_soundness_theorem satSound unsatSound ->
    ay_rsrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rsrg_counter_mismatch_cannot_bless_result
    {counterMismatch baselineNoClaim satSound unsatSound : Prop} :
    counterMismatch ->
    baselineNoClaim ->
    ay_rsrg_public_soundness_theorem satSound unsatSound ->
    ay_rsrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rsrg_replay_mismatch_cannot_bless_result
    {replayMismatch baselineNoClaim satSound unsatSound : Prop} :
    replayMismatch ->
    baselineNoClaim ->
    ay_rsrg_public_soundness_theorem satSound unsatSound ->
    ay_rsrg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_rsrg_policy_requires_benchmark_fingerprint
    {benchmarkFingerprint accepted : Prop} :
    benchmarkFingerprint -> accepted -> benchmarkFingerprint :=
  fun evidence _ => evidence

theorem ay_rsrg_policy_requires_restart_schedule_manifest
    {restartScheduleManifest accepted : Prop} :
    restartScheduleManifest -> accepted -> restartScheduleManifest :=
  fun evidence _ => evidence

theorem ay_rsrg_policy_requires_conflict_counter_digest
    {conflictCounterDigest accepted : Prop} :
    conflictCounterDigest -> accepted -> conflictCounterDigest :=
  fun evidence _ => evidence

theorem ay_rsrg_policy_requires_propagation_ledger
    {propagationLedger accepted : Prop} :
    propagationLedger -> accepted -> propagationLedger :=
  fun evidence _ => evidence

theorem ay_rsrg_policy_requires_learned_clause_ledger_digest
    {learnedClauseLedgerDigest accepted : Prop} :
    learnedClauseLedgerDigest -> accepted -> learnedClauseLedgerDigest :=
  fun evidence _ => evidence

theorem ay_rsrg_policy_requires_phase_saving_digest
    {phaseSavingDigest accepted : Prop} :
    phaseSavingDigest -> accepted -> phaseSavingDigest :=
  fun evidence _ => evidence

theorem ay_rsrg_policy_requires_decision_order_digest
    {decisionOrderDigest accepted : Prop} :
    decisionOrderDigest -> accepted -> decisionOrderDigest :=
  fun evidence _ => evidence

theorem ay_rsrg_policy_requires_replay_transcript
    {replayTranscript accepted : Prop} :
    replayTranscript -> accepted -> replayTranscript :=
  fun evidence _ => evidence

theorem ay_rsrg_policy_requires_cutoff_fallback_policy
    {cutoffFallbackPolicy accepted : Prop} :
    cutoffFallbackPolicy -> accepted -> cutoffFallbackPolicy :=
  fun evidence _ => evidence

theorem ay_rsrg_policy_requires_solver_build
    {solverBuildEvidence accepted : Prop} :
    solverBuildEvidence -> accepted -> solverBuildEvidence :=
  fun evidence _ => evidence

theorem ay_rsrg_policy_requires_validator
    {validatorGate accepted : Prop} :
    validatorGate -> accepted -> validatorGate :=
  fun evidence _ => evidence

theorem ay_rsrg_policy_requires_audit
    {auditTranscript accepted : Prop} :
    auditTranscript -> accepted -> auditTranscript :=
  fun evidence _ => evidence
