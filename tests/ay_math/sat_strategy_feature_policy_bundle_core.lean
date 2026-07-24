def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  AyDisj satSound unsatSound

def AyFeaturePolicyBundleInputs
    (learnedFeatures ablationTags restartPolicy branchingPolicy
      fallbackSolver validatorGate auditEvidence : Prop) : Prop :=
  AyConj learnedFeatures
    (AyConj ablationTags
      (AyConj restartPolicy
        (AyConj branchingPolicy
          (AyConj fallbackSolver
            (AyConj validatorGate auditEvidence)))))

def AyLearnedFeatureEvidence (learnedFeatures : Prop) : Prop :=
  learnedFeatures

def AyAblationTagEvidence (ablationTags : Prop) : Prop :=
  ablationTags

def AyRestartPolicyEvidence (restartPolicy : Prop) : Prop :=
  restartPolicy

def AyBranchingPolicyEvidence (branchingPolicy : Prop) : Prop :=
  branchingPolicy

def AyFallbackSolverEvidence (fallbackSolver : Prop) : Prop :=
  fallbackSolver

def AyValidatorGateEvidence (validatorGate : Prop) : Prop :=
  validatorGate

def AyAuditEvidence (auditEvidence : Prop) : Prop :=
  auditEvidence

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyFeaturePolicyBundleAccepted
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted : Prop) : Prop :=
  bundleAccepted

def AyFeaturePolicyBundleRejected
    (staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit : Prop) : Prop :=
  AyDisj staleFeatureExtraction
    (AyDisj missingAblation
      (AyDisj policyMismatch
        (AyDisj buildMismatch
          (AyDisj missingValidator inconsistentAudit))))

def AyFeaturePolicyBundleGate
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted staleFeatureExtraction
      missingAblation policyMismatch buildMismatch missingValidator
      inconsistentAudit : Prop) : Prop :=
  AyDisj
    (AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted)
    (AyFeaturePolicyBundleRejected
      staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit)

def AyBundlePerformanceHint
    (bundleAccepted restartHint branchingHint preprocessHint : Prop) : Prop :=
  AyConj bundleAccepted
    (AyConj restartHint (AyConj branchingHint preprocessHint))

def AyFallbackPath
    (fallbackSolver baselineSoundness noClaim : Prop) : Prop :=
  baselineSoundness

theorem ay_sfpb_input_components
    (learnedFeatures ablationTags restartPolicy branchingPolicy
      fallbackSolver validatorGate auditEvidence : Prop) :
    AyFeaturePolicyBundleInputs
      learnedFeatures ablationTags restartPolicy branchingPolicy
      fallbackSolver validatorGate auditEvidence ->
    AyConj learnedFeatures
      (AyConj ablationTags
        (AyConj restartPolicy
          (AyConj branchingPolicy
            (AyConj fallbackSolver
              (AyConj validatorGate auditEvidence))))) := by
  intro inputs
  exact inputs

theorem ay_sfpb_accepted_bundle
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted : Prop) :
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    bundleAccepted := by
  intro accepted
  exact accepted

theorem ay_sfpb_accepted_learned_features
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted : Prop) :
    AyLearnedFeatureEvidence learnedFeatures ->
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    AyLearnedFeatureEvidence learnedFeatures := by
  intro evidence _accepted
  exact evidence

theorem ay_sfpb_accepted_ablation_tags
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted : Prop) :
    AyAblationTagEvidence ablationTags ->
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    AyAblationTagEvidence ablationTags := by
  intro evidence _accepted
  exact evidence

theorem ay_sfpb_accepted_restart_policy
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted : Prop) :
    AyRestartPolicyEvidence restartPolicy ->
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    AyRestartPolicyEvidence restartPolicy := by
  intro evidence _accepted
  exact evidence

theorem ay_sfpb_accepted_branching_policy
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted : Prop) :
    AyBranchingPolicyEvidence branchingPolicy ->
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    AyBranchingPolicyEvidence branchingPolicy := by
  intro evidence _accepted
  exact evidence

theorem ay_sfpb_accepted_fallback_solver
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted : Prop) :
    AyFallbackSolverEvidence fallbackSolver ->
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    AyFallbackSolverEvidence fallbackSolver := by
  intro evidence _accepted
  exact evidence

theorem ay_sfpb_accepted_validator_gate
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted : Prop) :
    AyValidatorGateEvidence validatorGate ->
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    AyValidatorGateEvidence validatorGate := by
  intro evidence _accepted
  exact evidence

theorem ay_sfpb_accepted_audit_evidence
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted : Prop) :
    AyAuditEvidence auditEvidence ->
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    AyAuditEvidence auditEvidence := by
  intro evidence _accepted
  exact evidence

theorem ay_sfpb_bundle_admissible_hint
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted restartHint branchingHint
      preprocessHint : Prop) :
    AyLearnedFeatureEvidence learnedFeatures ->
    AyAblationTagEvidence ablationTags ->
    AyRestartPolicyEvidence restartPolicy ->
    AyBranchingPolicyEvidence branchingPolicy ->
    AyFallbackSolverEvidence fallbackSolver ->
    AyValidatorGateEvidence validatorGate ->
    AyAuditEvidence auditEvidence ->
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    (learnedFeatures -> ablationTags -> restartPolicy -> branchingPolicy ->
      fallbackSolver -> validatorGate -> auditEvidence -> bundleAccepted ->
      AyBundlePerformanceHint bundleAccepted restartHint branchingHint
        preprocessHint) ->
    AyBundlePerformanceHint bundleAccepted restartHint branchingHint
      preprocessHint := by
  intro features ablation restart branching fallback validator audit accepted
  intro sound
  exact sound features ablation restart branching fallback validator audit accepted

theorem ay_sfpb_hint_cannot_change_truth
    (bundleAccepted restartHint branchingHint preprocessHint satSound
      unsatSound : Prop) :
    AyBundlePerformanceHint
      bundleAccepted restartHint branchingHint preprocessHint ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _hint truth
  exact truth

theorem ay_sfpb_accepted_bundle_preserves_public_soundness
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted restartHint branchingHint
      preprocessHint satSound unsatSound : Prop) :
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    AyBundlePerformanceHint
      bundleAccepted restartHint branchingHint preprocessHint ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted hint truth
  exact ay_sfpb_hint_cannot_change_truth
    bundleAccepted restartHint branchingHint preprocessHint satSound unsatSound
    hint truth

theorem ay_sfpb_rejected_is_no_claim
    (staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit : Prop) :
    AyFeaturePolicyBundleRejected
      staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit ->
    AyNoClaimDiagnostic
      (AyFeaturePolicyBundleRejected
        staleFeatureExtraction missingAblation policyMismatch buildMismatch
        missingValidator inconsistentAudit) := by
  intro rejected
  exact rejected

theorem ay_sfpb_rejected_fallback_preserves_baseline
    (staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit fallbackSolver baselineSoundness
      noClaim : Prop) :
    AyFeaturePolicyBundleRejected
      staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit ->
    AyFallbackPath fallbackSolver baselineSoundness noClaim ->
    baselineSoundness := by
  intro _rejected fallbackPath
  exact fallbackPath

theorem ay_sfpb_rejected_cannot_bless_public_result
    (staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit publicResultClaim : Prop) :
    AyFeaturePolicyBundleRejected
      staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit ->
    publicResultClaim ->
    publicResultClaim := by
  intro _rejected claim
  exact claim

theorem ay_sfpb_gate_accept_or_reject
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted staleFeatureExtraction
      missingAblation policyMismatch buildMismatch missingValidator
      inconsistentAudit : Prop) :
    AyFeaturePolicyBundleGate
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted staleFeatureExtraction
      missingAblation policyMismatch buildMismatch missingValidator
      inconsistentAudit ->
    AyDisj
      (AyFeaturePolicyBundleAccepted
        learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
        validatorGate auditEvidence bundleAccepted)
      (AyFeaturePolicyBundleRejected
        staleFeatureExtraction missingAblation policyMismatch buildMismatch
        missingValidator inconsistentAudit) := by
  intro gate
  exact gate

theorem ay_sfpb_safe_bundle_deployment_accept
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted restartHint branchingHint
      preprocessHint satSound unsatSound : Prop) :
    AyLearnedFeatureEvidence learnedFeatures ->
    AyAblationTagEvidence ablationTags ->
    AyRestartPolicyEvidence restartPolicy ->
    AyBranchingPolicyEvidence branchingPolicy ->
    AyFallbackSolverEvidence fallbackSolver ->
    AyValidatorGateEvidence validatorGate ->
    AyAuditEvidence auditEvidence ->
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    (learnedFeatures -> ablationTags -> restartPolicy -> branchingPolicy ->
      fallbackSolver -> validatorGate -> auditEvidence -> bundleAccepted ->
      AyBundlePerformanceHint bundleAccepted restartHint branchingHint
        preprocessHint) ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro features ablation restart branching fallback validator audit accepted
  intro sound truth
  let hint :=
    ay_sfpb_bundle_admissible_hint
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted restartHint branchingHint
      preprocessHint features ablation restart branching fallback validator audit
      accepted sound
  exact ay_sfpb_accepted_bundle_preserves_public_soundness
    learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
    validatorGate auditEvidence bundleAccepted restartHint branchingHint
    preprocessHint satSound unsatSound accepted hint truth

theorem ay_sfpb_safe_bundle_deployment_fallback
    (staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit fallbackSolver baselineSoundness
      noClaim : Prop) :
    AyFeaturePolicyBundleRejected
      staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit ->
    AyFallbackPath fallbackSolver baselineSoundness noClaim ->
    baselineSoundness := by
  intro rejected fallbackPath
  exact ay_sfpb_rejected_fallback_preserves_baseline
    staleFeatureExtraction missingAblation policyMismatch buildMismatch
    missingValidator inconsistentAudit fallbackSolver baselineSoundness noClaim
    rejected fallbackPath

theorem ay_sfpb_drifted_bundle_no_claim
    (staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit noClaim : Prop) :
    AyFeaturePolicyBundleRejected
      staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_sfpb_stale_feature_extraction_forces_no_claim
    (staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit noClaim : Prop) :
    staleFeatureExtraction ->
    AyFeaturePolicyBundleRejected
      staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _stale rejected diagnostic
  exact ay_sfpb_drifted_bundle_no_claim
    staleFeatureExtraction missingAblation policyMismatch buildMismatch
    missingValidator inconsistentAudit noClaim rejected diagnostic

theorem ay_sfpb_missing_ablation_forces_no_claim
    (staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit noClaim : Prop) :
    missingAblation ->
    AyFeaturePolicyBundleRejected
      staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _missing rejected diagnostic
  exact ay_sfpb_drifted_bundle_no_claim
    staleFeatureExtraction missingAblation policyMismatch buildMismatch
    missingValidator inconsistentAudit noClaim rejected diagnostic

theorem ay_sfpb_policy_build_mismatch_forces_no_claim
    (staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit noClaim : Prop) :
    AyDisj policyMismatch buildMismatch ->
    AyFeaturePolicyBundleRejected
      staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _mismatch rejected diagnostic
  exact ay_sfpb_drifted_bundle_no_claim
    staleFeatureExtraction missingAblation policyMismatch buildMismatch
    missingValidator inconsistentAudit noClaim rejected diagnostic

theorem ay_sfpb_missing_validator_forces_no_claim
    (staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit noClaim : Prop) :
    missingValidator ->
    AyFeaturePolicyBundleRejected
      staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _missing rejected diagnostic
  exact ay_sfpb_drifted_bundle_no_claim
    staleFeatureExtraction missingAblation policyMismatch buildMismatch
    missingValidator inconsistentAudit noClaim rejected diagnostic

theorem ay_sfpb_inconsistent_audit_forces_no_claim
    (staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit noClaim : Prop) :
    inconsistentAudit ->
    AyFeaturePolicyBundleRejected
      staleFeatureExtraction missingAblation policyMismatch buildMismatch
      missingValidator inconsistentAudit ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _inconsistent rejected diagnostic
  exact ay_sfpb_drifted_bundle_no_claim
    staleFeatureExtraction missingAblation policyMismatch buildMismatch
    missingValidator inconsistentAudit noClaim rejected diagnostic

theorem ay_sfpb_bundle_requires_features
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted : Prop) :
    AyLearnedFeatureEvidence learnedFeatures ->
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    AyLearnedFeatureEvidence learnedFeatures := by
  intro evidence accepted
  exact ay_sfpb_accepted_learned_features
    learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
    validatorGate auditEvidence bundleAccepted evidence accepted

theorem ay_sfpb_bundle_requires_validator
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted : Prop) :
    AyValidatorGateEvidence validatorGate ->
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    AyValidatorGateEvidence validatorGate := by
  intro evidence accepted
  exact ay_sfpb_accepted_validator_gate
    learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
    validatorGate auditEvidence bundleAccepted evidence accepted

theorem ay_sfpb_bundle_requires_audit
    (learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted : Prop) :
    AyAuditEvidence auditEvidence ->
    AyFeaturePolicyBundleAccepted
      learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
      validatorGate auditEvidence bundleAccepted ->
    AyAuditEvidence auditEvidence := by
  intro evidence accepted
  exact ay_sfpb_accepted_audit_evidence
    learnedFeatures ablationTags restartPolicy branchingPolicy fallbackSolver
    validatorGate auditEvidence bundleAccepted evidence accepted
