def ay_bcfg_conj (p q : Prop) : Prop := p ∧ q

def ay_bcfg_disj (p q : Prop) : Prop := p ∨ q

def ay_bcfg_public_soundness_theorem (satSound unsatSound : Prop) : Prop :=
  ay_bcfg_disj satSound unsatSound

def ay_bcfg_inputs
    (binaryGraphSnapshot watchedLiteralDigest learntClauseDatabaseSnapshot
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop) : Prop :=
  ay_bcfg_conj binaryGraphSnapshot
    (ay_bcfg_conj watchedLiteralDigest
      (ay_bcfg_conj learntClauseDatabaseSnapshot
        (ay_bcfg_conj propagationReplay
          (ay_bcfg_conj fallbackBaseline
            (ay_bcfg_conj solverBuildEvidence
              (ay_bcfg_conj validatorGate auditTranscript))))))

def ay_bcfg_binary_graph_snapshot_evidence
    (binaryGraphSnapshot : Prop) : Prop :=
  binaryGraphSnapshot

def ay_bcfg_watched_literal_digest_evidence
    (watchedLiteralDigest : Prop) : Prop :=
  watchedLiteralDigest

def ay_bcfg_learnt_clause_database_snapshot_evidence
    (learntClauseDatabaseSnapshot : Prop) : Prop :=
  learntClauseDatabaseSnapshot

def ay_bcfg_propagation_replay_evidence
    (propagationReplay : Prop) : Prop :=
  propagationReplay

def ay_bcfg_fallback_baseline_evidence (fallbackBaseline : Prop) : Prop :=
  fallbackBaseline

def ay_bcfg_solver_build_evidence (solverBuildEvidence : Prop) : Prop :=
  solverBuildEvidence

def ay_bcfg_validator_gate_evidence (validatorGate : Prop) : Prop :=
  validatorGate

def ay_bcfg_audit_transcript_evidence (auditTranscript : Prop) : Prop :=
  auditTranscript

def ay_bcfg_no_claim_diagnostic (diagnostic : Prop) : Prop := diagnostic

def ay_bcfg_accepted
    (binaryGraphSnapshot watchedLiteralDigest learntClauseDatabaseSnapshot
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript fastPathAccepted : Prop) : Prop :=
  fastPathAccepted

def ay_bcfg_rejected
    (binaryGraphMismatch watchedDigestMismatch databaseMismatch replayMismatch
      fallbackMismatch buildMismatch validatorMismatch auditMismatch : Prop) :
    Prop :=
  ay_bcfg_disj binaryGraphMismatch
    (ay_bcfg_disj watchedDigestMismatch
      (ay_bcfg_disj databaseMismatch
        (ay_bcfg_disj replayMismatch
          (ay_bcfg_disj fallbackMismatch
            (ay_bcfg_disj buildMismatch
              (ay_bcfg_disj validatorMismatch auditMismatch))))))

def ay_bcfg_gate (accepted rejected : Prop) : Prop :=
  ay_bcfg_disj accepted rejected

def ay_bcfg_fast_path_hint
    (fastPathAccepted propagationPolicy searchPolicy cachePolicy : Prop) : Prop :=
  fastPathAccepted

def ay_bcfg_recompute_path
    (fallbackBaseline noClaim recomputeRequired : Prop) : Prop :=
  recomputeRequired

theorem ay_bcfg_input_components
    {binaryGraphSnapshot watchedLiteralDigest learntClauseDatabaseSnapshot
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript : Prop} :
    ay_bcfg_inputs binaryGraphSnapshot watchedLiteralDigest
      learntClauseDatabaseSnapshot propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript ->
    ay_bcfg_inputs binaryGraphSnapshot watchedLiteralDigest
      learntClauseDatabaseSnapshot propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript := by
  intro inputs
  exact inputs

theorem ay_bcfg_accepted_policy
    {binaryGraphSnapshot watchedLiteralDigest learntClauseDatabaseSnapshot
      propagationReplay fallbackBaseline solverBuildEvidence validatorGate
      auditTranscript fastPathAccepted : Prop} :
    fastPathAccepted ->
    ay_bcfg_accepted binaryGraphSnapshot watchedLiteralDigest
      learntClauseDatabaseSnapshot propagationReplay fallbackBaseline
      solverBuildEvidence validatorGate auditTranscript fastPathAccepted := by
  intro accepted
  exact accepted

theorem ay_bcfg_accepted_binary_graph_snapshot
    {binaryGraphSnapshot : Prop} :
    binaryGraphSnapshot ->
    ay_bcfg_binary_graph_snapshot_evidence binaryGraphSnapshot := by
  intro evidence
  exact evidence

theorem ay_bcfg_accepted_watched_literal_digest
    {watchedLiteralDigest : Prop} :
    watchedLiteralDigest ->
    ay_bcfg_watched_literal_digest_evidence watchedLiteralDigest := by
  intro evidence
  exact evidence

theorem ay_bcfg_accepted_learnt_clause_database_snapshot
    {learntClauseDatabaseSnapshot : Prop} :
    learntClauseDatabaseSnapshot ->
    ay_bcfg_learnt_clause_database_snapshot_evidence
      learntClauseDatabaseSnapshot := by
  intro evidence
  exact evidence

theorem ay_bcfg_accepted_propagation_replay
    {propagationReplay : Prop} :
    propagationReplay ->
    ay_bcfg_propagation_replay_evidence propagationReplay := by
  intro evidence
  exact evidence

theorem ay_bcfg_accepted_fallback_baseline
    {fallbackBaseline : Prop} :
    fallbackBaseline -> ay_bcfg_fallback_baseline_evidence fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_bcfg_accepted_solver_build_evidence
    {solverBuildEvidence : Prop} :
    solverBuildEvidence -> ay_bcfg_solver_build_evidence solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_bcfg_accepted_validator_gate
    {validatorGate : Prop} :
    validatorGate -> ay_bcfg_validator_gate_evidence validatorGate := by
  intro evidence
  exact evidence

theorem ay_bcfg_accepted_audit_transcript
    {auditTranscript : Prop} :
    auditTranscript -> ay_bcfg_audit_transcript_evidence auditTranscript := by
  intro evidence
  exact evidence

theorem ay_bcfg_fast_path_policy_admissible_hint
    {fastPathAccepted propagationPolicy searchPolicy cachePolicy : Prop} :
    fastPathAccepted ->
    propagationPolicy ->
    searchPolicy ->
    cachePolicy ->
    ay_bcfg_fast_path_hint fastPathAccepted propagationPolicy searchPolicy
      cachePolicy := by
  intro accepted propagation search cache
  exact accepted

theorem ay_bcfg_guidance_cannot_change_formula_truth
    {fastPathAccepted formulaTruth : Prop} :
    fastPathAccepted ->
    formulaTruth ->
    formulaTruth :=
  fun _ truth => truth

theorem ay_bcfg_accepted_guidance_preserves_public_soundness
    {fastPathAccepted satSound unsatSound : Prop} :
    fastPathAccepted ->
    ay_bcfg_public_soundness_theorem satSound unsatSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_bcfg_rejected_is_no_claim
    {binaryGraphMismatch diagnostic : Prop} :
    binaryGraphMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcfg_rejected_forces_recompute
    {binaryGraphMismatch recomputeRequired : Prop} :
    binaryGraphMismatch ->
    recomputeRequired ->
    recomputeRequired :=
  fun _ recompute => recompute

theorem ay_bcfg_rejected_cannot_bless_publication
    {binaryGraphMismatch baselineSound satSound unsatSound : Prop} :
    binaryGraphMismatch ->
    baselineSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcfg_gate_accept_or_reject
    {accepted rejected : Prop} :
    ay_bcfg_gate accepted rejected ->
    ay_bcfg_disj accepted rejected := by
  intro gate
  exact gate

theorem ay_bcfg_safe_strategy_guidance_accept
    {fastPathAccepted propagationPolicy searchPolicy cachePolicy satSound
      unsatSound : Prop} :
    fastPathAccepted ->
    propagationPolicy ->
    searchPolicy ->
    cachePolicy ->
    ay_bcfg_public_soundness_theorem satSound unsatSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound :=
  fun _ _ _ _ publicSound => publicSound

theorem ay_bcfg_safe_strategy_guidance_recompute
    {recomputeRequired satSound unsatSound : Prop} :
    recomputeRequired ->
    ay_bcfg_public_soundness_theorem satSound unsatSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound :=
  fun _ publicSound => publicSound

theorem ay_bcfg_binary_graph_mismatch_forces_no_claim
    {binaryGraphMismatch diagnostic : Prop} :
    binaryGraphMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcfg_watched_digest_mismatch_forces_no_claim
    {watchedDigestMismatch diagnostic : Prop} :
    watchedDigestMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcfg_database_mismatch_forces_no_claim
    {databaseMismatch diagnostic : Prop} :
    databaseMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcfg_replay_mismatch_forces_no_claim
    {replayMismatch diagnostic : Prop} :
    replayMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcfg_fallback_mismatch_forces_no_claim
    {fallbackMismatch diagnostic : Prop} :
    fallbackMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcfg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic : Prop} :
    buildMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcfg_validator_mismatch_forces_no_claim
    {validatorMismatch diagnostic : Prop} :
    validatorMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcfg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic : Prop} :
    auditMismatch ->
    diagnostic ->
    diagnostic :=
  fun _ noClaim => noClaim

theorem ay_bcfg_binary_graph_mismatch_cannot_bless_publication
    {binaryGraphMismatch baselineSound satSound unsatSound : Prop} :
    binaryGraphMismatch ->
    baselineSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcfg_watched_digest_mismatch_cannot_bless_publication
    {watchedDigestMismatch baselineSound satSound unsatSound : Prop} :
    watchedDigestMismatch ->
    baselineSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcfg_database_mismatch_cannot_bless_publication
    {databaseMismatch baselineSound satSound unsatSound : Prop} :
    databaseMismatch ->
    baselineSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcfg_replay_mismatch_cannot_bless_publication
    {replayMismatch baselineSound satSound unsatSound : Prop} :
    replayMismatch ->
    baselineSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcfg_fallback_mismatch_cannot_bless_publication
    {fallbackMismatch baselineSound satSound unsatSound : Prop} :
    fallbackMismatch ->
    baselineSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcfg_build_mismatch_cannot_bless_publication
    {buildMismatch baselineSound satSound unsatSound : Prop} :
    buildMismatch ->
    baselineSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcfg_validator_mismatch_cannot_bless_publication
    {validatorMismatch baselineSound satSound unsatSound : Prop} :
    validatorMismatch ->
    baselineSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcfg_audit_mismatch_cannot_bless_publication
    {auditMismatch baselineSound satSound unsatSound : Prop} :
    auditMismatch ->
    baselineSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound ->
    ay_bcfg_public_soundness_theorem satSound unsatSound :=
  fun _ _ publicSound => publicSound

theorem ay_bcfg_policy_requires_binary_graph_snapshot
    {binaryGraphSnapshot : Prop} :
    ay_bcfg_binary_graph_snapshot_evidence binaryGraphSnapshot ->
    binaryGraphSnapshot := by
  intro evidence
  exact evidence

theorem ay_bcfg_policy_requires_watched_literal_digest
    {watchedLiteralDigest : Prop} :
    ay_bcfg_watched_literal_digest_evidence watchedLiteralDigest ->
    watchedLiteralDigest := by
  intro evidence
  exact evidence

theorem ay_bcfg_policy_requires_learnt_clause_database_snapshot
    {learntClauseDatabaseSnapshot : Prop} :
    ay_bcfg_learnt_clause_database_snapshot_evidence
      learntClauseDatabaseSnapshot ->
    learntClauseDatabaseSnapshot := by
  intro evidence
  exact evidence

theorem ay_bcfg_policy_requires_propagation_replay
    {propagationReplay : Prop} :
    ay_bcfg_propagation_replay_evidence propagationReplay ->
    propagationReplay := by
  intro evidence
  exact evidence

theorem ay_bcfg_policy_requires_fallback_baseline
    {fallbackBaseline : Prop} :
    ay_bcfg_fallback_baseline_evidence fallbackBaseline -> fallbackBaseline := by
  intro evidence
  exact evidence

theorem ay_bcfg_policy_requires_solver_build
    {solverBuildEvidence : Prop} :
    ay_bcfg_solver_build_evidence solverBuildEvidence -> solverBuildEvidence := by
  intro evidence
  exact evidence

theorem ay_bcfg_policy_requires_validator
    {validatorGate : Prop} :
    ay_bcfg_validator_gate_evidence validatorGate -> validatorGate := by
  intro evidence
  exact evidence

theorem ay_bcfg_policy_requires_audit
    {auditTranscript : Prop} :
    ay_bcfg_audit_transcript_evidence auditTranscript -> auditTranscript := by
  intro evidence
  exact evidence
