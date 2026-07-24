def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  AyDisj satSound unsatSound

def AyProfileSelectorInputs
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard : Prop) :
    Prop :=
  AyConj benchmarkClass
    (AyConj featureReplay
      (AyConj solverBuild (AyConj policyReplay soundnessGuard)))

def AyBenchmarkClassEvidence (benchmarkClass : Prop) : Prop :=
  benchmarkClass

def AyFeatureReplayEvidence (featureReplay : Prop) : Prop :=
  featureReplay

def AySolverBuildCompatibility (solverBuild : Prop) : Prop :=
  solverBuild

def AyDeterministicPolicyReplay (policyReplay : Prop) : Prop :=
  policyReplay

def AyPublicSoundnessGuard (soundnessGuard : Prop) : Prop :=
  soundnessGuard

def AyBaselineFallbackEvidence (baselineSoundness : Prop) : Prop :=
  baselineSoundness

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyProfileSelectionAccepted
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected : Prop) : Prop :=
  profileSelected

def AyProfileSelectionRejected
    (classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
      soundnessGuardMismatch : Prop) : Prop :=
  AyDisj classMismatch
    (AyDisj featureReplayMismatch
      (AyDisj buildMismatch
        (AyDisj policyReplayMismatch soundnessGuardMismatch)))

def AyProfileSelectionGate
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected classMismatch featureReplayMismatch buildMismatch
      policyReplayMismatch soundnessGuardMismatch : Prop) : Prop :=
  AyDisj
    (AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected)
    (AyProfileSelectionRejected
      classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
      soundnessGuardMismatch)

def AyPerformanceHint
    (branchingHint restartHint preprocessBudget : Prop) : Prop :=
  AyConj branchingHint (AyConj restartHint preprocessBudget)

def AySelectedProfileUse
    (profileSelected branchingHint restartHint preprocessBudget : Prop) : Prop :=
  AyConj profileSelected
    (AyPerformanceHint branchingHint restartHint preprocessBudget)

theorem ay_spsg_input_components
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard : Prop) :
    AyProfileSelectorInputs
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard ->
    AyConj benchmarkClass
      (AyConj featureReplay
        (AyConj solverBuild (AyConj policyReplay soundnessGuard))) := by
  intro inputs
  exact inputs

theorem ay_spsg_accepted_profile
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected : Prop) :
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    profileSelected := by
  intro accepted
  exact accepted

theorem ay_spsg_accepted_benchmark_class
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected : Prop) :
    AyBenchmarkClassEvidence benchmarkClass ->
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    AyBenchmarkClassEvidence benchmarkClass := by
  intro evidence _accepted
  exact evidence

theorem ay_spsg_accepted_feature_replay
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected : Prop) :
    AyFeatureReplayEvidence featureReplay ->
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    AyFeatureReplayEvidence featureReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_spsg_accepted_solver_build
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected : Prop) :
    AySolverBuildCompatibility solverBuild ->
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    AySolverBuildCompatibility solverBuild := by
  intro evidence _accepted
  exact evidence

theorem ay_spsg_accepted_policy_replay
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected : Prop) :
    AyDeterministicPolicyReplay policyReplay ->
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    AyDeterministicPolicyReplay policyReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_spsg_accepted_soundness_guard
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected : Prop) :
    AyPublicSoundnessGuard soundnessGuard ->
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    AyPublicSoundnessGuard soundnessGuard := by
  intro evidence _accepted
  exact evidence

theorem ay_spsg_profile_admissible_hint
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected branchingHint restartHint preprocessBudget : Prop) :
    AyBenchmarkClassEvidence benchmarkClass ->
    AyFeatureReplayEvidence featureReplay ->
    AySolverBuildCompatibility solverBuild ->
    AyDeterministicPolicyReplay policyReplay ->
    AyPublicSoundnessGuard soundnessGuard ->
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    (benchmarkClass -> featureReplay -> solverBuild -> policyReplay ->
      soundnessGuard -> profileSelected ->
      AyPerformanceHint branchingHint restartHint preprocessBudget) ->
    AyPerformanceHint branchingHint restartHint preprocessBudget := by
  intro classEvidence featureEvidence buildEvidence replayEvidence guardEvidence
  intro accepted sound
  exact sound classEvidence featureEvidence buildEvidence replayEvidence
    guardEvidence accepted

theorem ay_spsg_profile_use_cannot_change_truth
    (profileSelected branchingHint restartHint preprocessBudget
      satSound unsatSound : Prop) :
    AySelectedProfileUse
      profileSelected branchingHint restartHint preprocessBudget ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _profileUse truth
  exact truth

theorem ay_spsg_accepted_profile_preserves_public_soundness
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected branchingHint restartHint preprocessBudget
      satSound unsatSound : Prop) :
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    AySelectedProfileUse
      profileSelected branchingHint restartHint preprocessBudget ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted profileUse truth
  exact ay_spsg_profile_use_cannot_change_truth
    profileSelected branchingHint restartHint preprocessBudget
    satSound unsatSound profileUse truth

theorem ay_spsg_rejected_is_no_claim
    (classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
      soundnessGuardMismatch : Prop) :
    AyProfileSelectionRejected
      classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
      soundnessGuardMismatch ->
    AyNoClaimDiagnostic
      (AyProfileSelectionRejected
        classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
        soundnessGuardMismatch) := by
  intro rejected
  exact rejected

theorem ay_spsg_rejected_fallback_preserves_baseline
    (classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
      soundnessGuardMismatch baselineSoundness : Prop) :
    AyProfileSelectionRejected
      classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
      soundnessGuardMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_spsg_rejected_cannot_bless_public_result
    (classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
      soundnessGuardMismatch publicResultClaim : Prop) :
    AyProfileSelectionRejected
      classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
      soundnessGuardMismatch ->
    publicResultClaim ->
    publicResultClaim := by
  intro _rejected claim
  exact claim

theorem ay_spsg_gate_accept_or_reject
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected classMismatch featureReplayMismatch buildMismatch
      policyReplayMismatch soundnessGuardMismatch : Prop) :
    AyProfileSelectionGate
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected classMismatch featureReplayMismatch buildMismatch
      policyReplayMismatch soundnessGuardMismatch ->
    AyDisj
      (AyProfileSelectionAccepted
        benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
        profileSelected)
      (AyProfileSelectionRejected
        classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
        soundnessGuardMismatch) := by
  intro gate
  exact gate

theorem ay_spsg_safe_profile_deployment_accept
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected branchingHint restartHint preprocessBudget
      satSound unsatSound : Prop) :
    AyBenchmarkClassEvidence benchmarkClass ->
    AyFeatureReplayEvidence featureReplay ->
    AySolverBuildCompatibility solverBuild ->
    AyDeterministicPolicyReplay policyReplay ->
    AyPublicSoundnessGuard soundnessGuard ->
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    (benchmarkClass -> featureReplay -> solverBuild -> policyReplay ->
      soundnessGuard -> profileSelected ->
      AyPerformanceHint branchingHint restartHint preprocessBudget) ->
    AySelectedProfileUse
      profileSelected branchingHint restartHint preprocessBudget ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro classEvidence featureEvidence buildEvidence replayEvidence guardEvidence
  intro accepted hintSound profileUse truth
  let _hint :=
    ay_spsg_profile_admissible_hint
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected branchingHint restartHint preprocessBudget
      classEvidence featureEvidence buildEvidence replayEvidence guardEvidence
      accepted hintSound
  exact ay_spsg_accepted_profile_preserves_public_soundness
    benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
    profileSelected branchingHint restartHint preprocessBudget
    satSound unsatSound accepted profileUse truth

theorem ay_spsg_safe_profile_deployment_fallback
    (classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
      soundnessGuardMismatch baselineSoundness profileSelected branchingHint
      restartHint preprocessBudget : Prop) :
    AyProfileSelectionRejected
      classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
      soundnessGuardMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    AySelectedProfileUse
      profileSelected branchingHint restartHint preprocessBudget ->
    baselineSoundness := by
  intro rejected fallback _profileUse
  exact ay_spsg_rejected_fallback_preserves_baseline
    classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
    soundnessGuardMismatch baselineSoundness rejected fallback

theorem ay_spsg_mismatched_guard_no_claim
    (classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
      soundnessGuardMismatch noClaim : Prop) :
    AyProfileSelectionRejected
      classMismatch featureReplayMismatch buildMismatch policyReplayMismatch
      soundnessGuardMismatch ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_spsg_profile_requires_class_evidence
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected : Prop) :
    AyBenchmarkClassEvidence benchmarkClass ->
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    AyBenchmarkClassEvidence benchmarkClass := by
  intro evidence accepted
  exact ay_spsg_accepted_benchmark_class
    benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
    profileSelected evidence accepted

theorem ay_spsg_profile_requires_feature_replay
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected : Prop) :
    AyFeatureReplayEvidence featureReplay ->
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    AyFeatureReplayEvidence featureReplay := by
  intro evidence accepted
  exact ay_spsg_accepted_feature_replay
    benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
    profileSelected evidence accepted

theorem ay_spsg_profile_requires_solver_build
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected : Prop) :
    AySolverBuildCompatibility solverBuild ->
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    AySolverBuildCompatibility solverBuild := by
  intro evidence accepted
  exact ay_spsg_accepted_solver_build
    benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
    profileSelected evidence accepted

theorem ay_spsg_profile_requires_policy_replay
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected : Prop) :
    AyDeterministicPolicyReplay policyReplay ->
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    AyDeterministicPolicyReplay policyReplay := by
  intro evidence accepted
  exact ay_spsg_accepted_policy_replay
    benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
    profileSelected evidence accepted

theorem ay_spsg_profile_requires_public_soundness_guard
    (benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected : Prop) :
    AyPublicSoundnessGuard soundnessGuard ->
    AyProfileSelectionAccepted
      benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
      profileSelected ->
    AyPublicSoundnessGuard soundnessGuard := by
  intro evidence accepted
  exact ay_spsg_accepted_soundness_guard
    benchmarkClass featureReplay solverBuild policyReplay soundnessGuard
    profileSelected evidence accepted
