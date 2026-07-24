def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  AyDisj satSound unsatSound

def AyInstanceClassPolicyInputs
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence : Prop) : Prop :=
  AyConj classEvidence
    (AyConj featureSchema
      (AyConj classifierReplay
        (AyConj solverBuild
          (AyConj policyTranscript
            (AyConj soundnessGuard fallbackEvidence)))))

def AyClassEvidence (classEvidence : Prop) : Prop :=
  classEvidence

def AyFeatureSchemaEvidence (featureSchema : Prop) : Prop :=
  featureSchema

def AyClassifierReplayEvidence (classifierReplay : Prop) : Prop :=
  classifierReplay

def AySolverBuildEvidence (solverBuild : Prop) : Prop :=
  solverBuild

def AyPolicyTranscriptEvidence (policyTranscript : Prop) : Prop :=
  policyTranscript

def AyPublicSoundnessGuardEvidence (soundnessGuard : Prop) : Prop :=
  soundnessGuard

def AyFallbackEvidence (fallbackEvidence : Prop) : Prop :=
  fallbackEvidence

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyInstanceClassPolicyAccepted
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) : Prop :=
  policyAccepted

def AyInstanceClassPolicyRejected
    (classDrift schemaMismatch classifierReplayMismatch buildMismatch
      transcriptMismatch missingFallback : Prop) : Prop :=
  AyDisj classDrift
    (AyDisj schemaMismatch
      (AyDisj classifierReplayMismatch
        (AyDisj buildMismatch (AyDisj transcriptMismatch missingFallback))))

def AyInstanceClassPolicyGate
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted classDrift schemaMismatch
      classifierReplayMismatch buildMismatch transcriptMismatch missingFallback :
      Prop) : Prop :=
  AyDisj
    (AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted)
    (AyInstanceClassPolicyRejected
      classDrift schemaMismatch classifierReplayMismatch buildMismatch
      transcriptMismatch missingFallback)

def AyPolicyPerformanceHint
    (policyAccepted branching restart preprocessing : Prop) : Prop :=
  AyConj policyAccepted (AyConj branching (AyConj restart preprocessing))

def AyOptimizationPath
    (branching restart preprocessing selectedPolicy : Prop) : Prop :=
  AyConj branching (AyConj restart (AyConj preprocessing selectedPolicy))

theorem ay_sicp_input_components
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence : Prop) :
    AyInstanceClassPolicyInputs
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence ->
    AyConj classEvidence
      (AyConj featureSchema
        (AyConj classifierReplay
          (AyConj solverBuild
            (AyConj policyTranscript
              (AyConj soundnessGuard fallbackEvidence))))) := by
  intro inputs
  exact inputs

theorem ay_sicp_accepted_policy
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    policyAccepted := by
  intro accepted
  exact accepted

theorem ay_sicp_accepted_class_evidence
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AyClassEvidence classEvidence ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AyClassEvidence classEvidence := by
  intro evidence _accepted
  exact evidence

theorem ay_sicp_accepted_feature_schema
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AyFeatureSchemaEvidence featureSchema ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AyFeatureSchemaEvidence featureSchema := by
  intro evidence _accepted
  exact evidence

theorem ay_sicp_accepted_classifier_replay
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AyClassifierReplayEvidence classifierReplay ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AyClassifierReplayEvidence classifierReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_sicp_accepted_solver_build
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AySolverBuildEvidence solverBuild ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AySolverBuildEvidence solverBuild := by
  intro evidence _accepted
  exact evidence

theorem ay_sicp_accepted_policy_transcript
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AyPolicyTranscriptEvidence policyTranscript ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AyPolicyTranscriptEvidence policyTranscript := by
  intro evidence _accepted
  exact evidence

theorem ay_sicp_accepted_soundness_guard
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AyPublicSoundnessGuardEvidence soundnessGuard := by
  intro evidence _accepted
  exact evidence

theorem ay_sicp_accepted_fallback_evidence
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AyFallbackEvidence fallbackEvidence ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AyFallbackEvidence fallbackEvidence := by
  intro evidence _accepted
  exact evidence

theorem ay_sicp_policy_admissible_hint
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted branching restart
      preprocessing : Prop) :
    AyClassEvidence classEvidence ->
    AyFeatureSchemaEvidence featureSchema ->
    AyClassifierReplayEvidence classifierReplay ->
    AySolverBuildEvidence solverBuild ->
    AyPolicyTranscriptEvidence policyTranscript ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyFallbackEvidence fallbackEvidence ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    (classEvidence -> featureSchema -> classifierReplay -> solverBuild ->
      policyTranscript -> soundnessGuard -> fallbackEvidence ->
      policyAccepted -> AyPolicyPerformanceHint
        policyAccepted branching restart preprocessing) ->
    AyPolicyPerformanceHint policyAccepted branching restart preprocessing := by
  intro classEv schema replay build transcript guard fallback accepted sound
  exact sound classEv schema replay build transcript guard fallback accepted

theorem ay_sicp_hint_cannot_change_truth
    (policyAccepted branching restart preprocessing satSound unsatSound : Prop) :
    AyPolicyPerformanceHint policyAccepted branching restart preprocessing ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _hint truth
  exact truth

theorem ay_sicp_accepted_policy_preserves_public_soundness
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted branching restart
      preprocessing satSound unsatSound : Prop) :
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AyPolicyPerformanceHint policyAccepted branching restart preprocessing ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _accepted hint truth
  exact ay_sicp_hint_cannot_change_truth
    policyAccepted branching restart preprocessing satSound unsatSound hint truth

theorem ay_sicp_rejected_is_no_claim
    (classDrift schemaMismatch classifierReplayMismatch buildMismatch
      transcriptMismatch missingFallback : Prop) :
    AyInstanceClassPolicyRejected
      classDrift schemaMismatch classifierReplayMismatch buildMismatch
      transcriptMismatch missingFallback ->
    AyNoClaimDiagnostic
      (AyInstanceClassPolicyRejected
        classDrift schemaMismatch classifierReplayMismatch buildMismatch
        transcriptMismatch missingFallback) := by
  intro rejected
  exact rejected

theorem ay_sicp_rejected_fallback_preserves_baseline
    (classDrift schemaMismatch classifierReplayMismatch buildMismatch
      transcriptMismatch missingFallback baselineSoundness : Prop) :
    AyInstanceClassPolicyRejected
      classDrift schemaMismatch classifierReplayMismatch buildMismatch
      transcriptMismatch missingFallback ->
    AyFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_sicp_rejected_cannot_bless_public_result
    (classDrift schemaMismatch classifierReplayMismatch buildMismatch
      transcriptMismatch missingFallback publicResultClaim : Prop) :
    AyInstanceClassPolicyRejected
      classDrift schemaMismatch classifierReplayMismatch buildMismatch
      transcriptMismatch missingFallback ->
    publicResultClaim ->
    publicResultClaim := by
  intro _rejected claim
  exact claim

theorem ay_sicp_gate_accept_or_reject
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted classDrift schemaMismatch
      classifierReplayMismatch buildMismatch transcriptMismatch missingFallback :
      Prop) :
    AyInstanceClassPolicyGate
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted classDrift schemaMismatch
      classifierReplayMismatch buildMismatch transcriptMismatch missingFallback ->
    AyDisj
      (AyInstanceClassPolicyAccepted
        classEvidence featureSchema classifierReplay solverBuild policyTranscript
        soundnessGuard fallbackEvidence policyAccepted)
      (AyInstanceClassPolicyRejected
        classDrift schemaMismatch classifierReplayMismatch buildMismatch
        transcriptMismatch missingFallback) := by
  intro gate
  exact gate

theorem ay_sicp_safe_policy_deployment_accept
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted branching restart
      preprocessing satSound unsatSound : Prop) :
    AyClassEvidence classEvidence ->
    AyFeatureSchemaEvidence featureSchema ->
    AyClassifierReplayEvidence classifierReplay ->
    AySolverBuildEvidence solverBuild ->
    AyPolicyTranscriptEvidence policyTranscript ->
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyFallbackEvidence fallbackEvidence ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    (classEvidence -> featureSchema -> classifierReplay -> solverBuild ->
      policyTranscript -> soundnessGuard -> fallbackEvidence ->
      policyAccepted -> AyPolicyPerformanceHint
        policyAccepted branching restart preprocessing) ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro classEv schema replay build transcript guard fallback accepted sound truth
  let hint :=
    ay_sicp_policy_admissible_hint
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted branching restart
      preprocessing classEv schema replay build transcript guard fallback
      accepted sound
  exact ay_sicp_accepted_policy_preserves_public_soundness
    classEvidence featureSchema classifierReplay solverBuild policyTranscript
    soundnessGuard fallbackEvidence policyAccepted branching restart
    preprocessing satSound unsatSound accepted hint truth

theorem ay_sicp_safe_policy_deployment_fallback
    (classDrift schemaMismatch classifierReplayMismatch buildMismatch
      transcriptMismatch missingFallback baselineSoundness branching restart
      preprocessing selectedPolicy : Prop) :
    AyInstanceClassPolicyRejected
      classDrift schemaMismatch classifierReplayMismatch buildMismatch
      transcriptMismatch missingFallback ->
    AyFallbackEvidence baselineSoundness ->
    AyOptimizationPath branching restart preprocessing selectedPolicy ->
    baselineSoundness := by
  intro rejected fallback _path
  exact ay_sicp_rejected_fallback_preserves_baseline
    classDrift schemaMismatch classifierReplayMismatch buildMismatch
    transcriptMismatch missingFallback baselineSoundness rejected fallback

theorem ay_sicp_mismatch_no_claim
    (classDrift schemaMismatch classifierReplayMismatch buildMismatch
      transcriptMismatch missingFallback noClaim : Prop) :
    AyInstanceClassPolicyRejected
      classDrift schemaMismatch classifierReplayMismatch buildMismatch
      transcriptMismatch missingFallback ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_sicp_policy_requires_class_evidence
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AyClassEvidence classEvidence ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AyClassEvidence classEvidence := by
  intro evidence accepted
  exact ay_sicp_accepted_class_evidence
    classEvidence featureSchema classifierReplay solverBuild policyTranscript
    soundnessGuard fallbackEvidence policyAccepted evidence accepted

theorem ay_sicp_policy_requires_feature_schema
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AyFeatureSchemaEvidence featureSchema ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AyFeatureSchemaEvidence featureSchema := by
  intro evidence accepted
  exact ay_sicp_accepted_feature_schema
    classEvidence featureSchema classifierReplay solverBuild policyTranscript
    soundnessGuard fallbackEvidence policyAccepted evidence accepted

theorem ay_sicp_policy_requires_classifier_replay
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AyClassifierReplayEvidence classifierReplay ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AyClassifierReplayEvidence classifierReplay := by
  intro evidence accepted
  exact ay_sicp_accepted_classifier_replay
    classEvidence featureSchema classifierReplay solverBuild policyTranscript
    soundnessGuard fallbackEvidence policyAccepted evidence accepted

theorem ay_sicp_policy_requires_solver_build
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AySolverBuildEvidence solverBuild ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AySolverBuildEvidence solverBuild := by
  intro evidence accepted
  exact ay_sicp_accepted_solver_build
    classEvidence featureSchema classifierReplay solverBuild policyTranscript
    soundnessGuard fallbackEvidence policyAccepted evidence accepted

theorem ay_sicp_policy_requires_transcript
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AyPolicyTranscriptEvidence policyTranscript ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AyPolicyTranscriptEvidence policyTranscript := by
  intro evidence accepted
  exact ay_sicp_accepted_policy_transcript
    classEvidence featureSchema classifierReplay solverBuild policyTranscript
    soundnessGuard fallbackEvidence policyAccepted evidence accepted

theorem ay_sicp_policy_requires_soundness_guard
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AyPublicSoundnessGuardEvidence soundnessGuard ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AyPublicSoundnessGuardEvidence soundnessGuard := by
  intro evidence accepted
  exact ay_sicp_accepted_soundness_guard
    classEvidence featureSchema classifierReplay solverBuild policyTranscript
    soundnessGuard fallbackEvidence policyAccepted evidence accepted

theorem ay_sicp_policy_requires_fallback_evidence
    (classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted : Prop) :
    AyFallbackEvidence fallbackEvidence ->
    AyInstanceClassPolicyAccepted
      classEvidence featureSchema classifierReplay solverBuild policyTranscript
      soundnessGuard fallbackEvidence policyAccepted ->
    AyFallbackEvidence fallbackEvidence := by
  intro evidence accepted
  exact ay_sicp_accepted_fallback_evidence
    classEvidence featureSchema classifierReplay solverBuild policyTranscript
    soundnessGuard fallbackEvidence policyAccepted evidence accepted
