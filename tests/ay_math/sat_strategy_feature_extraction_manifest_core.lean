def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyFeatureVector
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay : Prop) : Prop :=
  AyConj featureManifest
    (AyConj formulaFingerprint
      (AyConj parserEvidence
        (AyConj preprocessorEvidence deterministicReplay)))

def AyFeatureManifestEvidence (featureManifest : Prop) : Prop :=
  featureManifest

def AyFormulaFingerprintEvidence (formulaFingerprint : Prop) : Prop :=
  formulaFingerprint

def AyParserEvidence (parserEvidence : Prop) : Prop :=
  parserEvidence

def AyPreprocessorEvidence (preprocessorEvidence : Prop) : Prop :=
  preprocessorEvidence

def AyDeterministicReplayEvidence (deterministicReplay : Prop) : Prop :=
  deterministicReplay

def AyFallbackEvidence (baselineSoundness : Prop) : Prop :=
  baselineSoundness

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyFeatureExtractionAccepted
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible : Prop) : Prop :=
  featuresAdmissible

def AyFeatureExtractionRejected
    (staleFeatures partialVector fingerprintMismatch parserMismatch
      replayMismatch : Prop) : Prop :=
  AyDisj staleFeatures
    (AyDisj partialVector
      (AyDisj fingerprintMismatch (AyDisj parserMismatch replayMismatch)))

def AyFeatureExtractionGate
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible staleFeatures partialVector
      fingerprintMismatch parserMismatch replayMismatch : Prop) : Prop :=
  AyDisj
    (AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible)
    (AyFeatureExtractionRejected
      staleFeatures partialVector fingerprintMismatch parserMismatch
      replayMismatch)

def AyBenchmarkClassUse
    (featuresAdmissible classLabel profileSelection : Prop) : Prop :=
  AyConj featuresAdmissible (AyConj classLabel profileSelection)

theorem ay_sfem_vector_components
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay : Prop) :
    AyFeatureVector
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay ->
    AyConj featureManifest
      (AyConj formulaFingerprint
        (AyConj parserEvidence
          (AyConj preprocessorEvidence deterministicReplay))) := by
  intro vector
  exact vector

theorem ay_sfem_accepted_features_admissible
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible : Prop) :
    AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible ->
    featuresAdmissible := by
  intro accepted
  exact accepted

theorem ay_sfem_accepted_feature_manifest
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible : Prop) :
    AyFeatureManifestEvidence featureManifest ->
    AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible ->
    AyFeatureManifestEvidence featureManifest := by
  intro evidence _accepted
  exact evidence

theorem ay_sfem_accepted_formula_fingerprint
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro evidence _accepted
  exact evidence

theorem ay_sfem_accepted_parser_evidence
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible : Prop) :
    AyParserEvidence parserEvidence ->
    AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible ->
    AyParserEvidence parserEvidence := by
  intro evidence _accepted
  exact evidence

theorem ay_sfem_accepted_preprocessor_evidence
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible : Prop) :
    AyPreprocessorEvidence preprocessorEvidence ->
    AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible ->
    AyPreprocessorEvidence preprocessorEvidence := by
  intro evidence _accepted
  exact evidence

theorem ay_sfem_accepted_deterministic_replay
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible : Prop) :
    AyDeterministicReplayEvidence deterministicReplay ->
    AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible ->
    AyDeterministicReplayEvidence deterministicReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_sfem_feature_vector_admissible
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible : Prop) :
    AyFeatureManifestEvidence featureManifest ->
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyParserEvidence parserEvidence ->
    AyPreprocessorEvidence preprocessorEvidence ->
    AyDeterministicReplayEvidence deterministicReplay ->
    AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible ->
    (featureManifest -> formulaFingerprint -> parserEvidence ->
      preprocessorEvidence -> deterministicReplay -> featuresAdmissible) ->
    featuresAdmissible := by
  intro manifest fingerprint parser preprocessor replay _accepted sound
  exact sound manifest fingerprint parser preprocessor replay

theorem ay_sfem_admissible_features_may_select_class
    (featuresAdmissible classLabel profileSelection : Prop) :
    featuresAdmissible ->
    AyBenchmarkClassUse featuresAdmissible classLabel profileSelection ->
    featuresAdmissible := by
  intro admissible _classUse
  exact admissible

theorem ay_sfem_rejected_is_no_claim
    (staleFeatures partialVector fingerprintMismatch parserMismatch
      replayMismatch : Prop) :
    AyFeatureExtractionRejected
      staleFeatures partialVector fingerprintMismatch parserMismatch
      replayMismatch ->
    AyNoClaimDiagnostic
      (AyFeatureExtractionRejected
        staleFeatures partialVector fingerprintMismatch parserMismatch
        replayMismatch) := by
  intro rejected
  exact rejected

theorem ay_sfem_rejected_fallback_preserves_baseline
    (staleFeatures partialVector fingerprintMismatch parserMismatch
      replayMismatch baselineSoundness : Prop) :
    AyFeatureExtractionRejected
      staleFeatures partialVector fingerprintMismatch parserMismatch
      replayMismatch ->
    AyFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_sfem_rejected_cannot_bless_features
    (staleFeatures partialVector fingerprintMismatch parserMismatch
      replayMismatch featureSoundnessClaim : Prop) :
    AyFeatureExtractionRejected
      staleFeatures partialVector fingerprintMismatch parserMismatch
      replayMismatch ->
    featureSoundnessClaim ->
    featureSoundnessClaim := by
  intro _rejected claim
  exact claim

theorem ay_sfem_gate_accept_or_reject
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible staleFeatures partialVector
      fingerprintMismatch parserMismatch replayMismatch : Prop) :
    AyFeatureExtractionGate
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible staleFeatures partialVector
      fingerprintMismatch parserMismatch replayMismatch ->
    AyDisj
      (AyFeatureExtractionAccepted
        featureManifest formulaFingerprint parserEvidence preprocessorEvidence
        deterministicReplay featuresAdmissible)
      (AyFeatureExtractionRejected
        staleFeatures partialVector fingerprintMismatch parserMismatch
        replayMismatch) := by
  intro gate
  exact gate

theorem ay_sfem_safe_feature_deployment_accept
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible classLabel profileSelection : Prop) :
    AyFeatureManifestEvidence featureManifest ->
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyParserEvidence parserEvidence ->
    AyPreprocessorEvidence preprocessorEvidence ->
    AyDeterministicReplayEvidence deterministicReplay ->
    AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible ->
    (featureManifest -> formulaFingerprint -> parserEvidence ->
      preprocessorEvidence -> deterministicReplay -> featuresAdmissible) ->
    AyBenchmarkClassUse featuresAdmissible classLabel profileSelection ->
    featuresAdmissible := by
  intro manifest fingerprint parser preprocessor replay accepted sound classUse
  exact ay_sfem_admissible_features_may_select_class
    featuresAdmissible classLabel profileSelection
    (ay_sfem_feature_vector_admissible
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible manifest fingerprint parser
      preprocessor replay accepted sound)
    classUse

theorem ay_sfem_safe_feature_deployment_fallback
    (staleFeatures partialVector fingerprintMismatch parserMismatch
      replayMismatch baselineSoundness classLabel profileSelection : Prop) :
    AyFeatureExtractionRejected
      staleFeatures partialVector fingerprintMismatch parserMismatch
      replayMismatch ->
    AyFallbackEvidence baselineSoundness ->
    AyBenchmarkClassUse baselineSoundness classLabel profileSelection ->
    baselineSoundness := by
  intro rejected fallback _classUse
  exact ay_sfem_rejected_fallback_preserves_baseline
    staleFeatures partialVector fingerprintMismatch parserMismatch
    replayMismatch baselineSoundness rejected fallback

theorem ay_sfem_stale_or_partial_no_claim
    (staleFeatures partialVector fingerprintMismatch parserMismatch
      replayMismatch noClaim : Prop) :
    AyFeatureExtractionRejected
      staleFeatures partialVector fingerprintMismatch parserMismatch
      replayMismatch ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_sfem_features_require_manifest
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible : Prop) :
    AyFeatureManifestEvidence featureManifest ->
    AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible ->
    AyFeatureManifestEvidence featureManifest := by
  intro evidence accepted
  exact ay_sfem_accepted_feature_manifest
    featureManifest formulaFingerprint parserEvidence preprocessorEvidence
    deterministicReplay featuresAdmissible evidence accepted

theorem ay_sfem_features_require_fingerprint
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro evidence accepted
  exact ay_sfem_accepted_formula_fingerprint
    featureManifest formulaFingerprint parserEvidence preprocessorEvidence
    deterministicReplay featuresAdmissible evidence accepted

theorem ay_sfem_features_require_parser
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible : Prop) :
    AyParserEvidence parserEvidence ->
    AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible ->
    AyParserEvidence parserEvidence := by
  intro evidence accepted
  exact ay_sfem_accepted_parser_evidence
    featureManifest formulaFingerprint parserEvidence preprocessorEvidence
    deterministicReplay featuresAdmissible evidence accepted

theorem ay_sfem_features_require_preprocessor
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible : Prop) :
    AyPreprocessorEvidence preprocessorEvidence ->
    AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible ->
    AyPreprocessorEvidence preprocessorEvidence := by
  intro evidence accepted
  exact ay_sfem_accepted_preprocessor_evidence
    featureManifest formulaFingerprint parserEvidence preprocessorEvidence
    deterministicReplay featuresAdmissible evidence accepted

theorem ay_sfem_features_require_replay
    (featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible : Prop) :
    AyDeterministicReplayEvidence deterministicReplay ->
    AyFeatureExtractionAccepted
      featureManifest formulaFingerprint parserEvidence preprocessorEvidence
      deterministicReplay featuresAdmissible ->
    AyDeterministicReplayEvidence deterministicReplay := by
  intro evidence accepted
  exact ay_sfem_accepted_deterministic_replay
    featureManifest formulaFingerprint parserEvidence preprocessorEvidence
    deterministicReplay featuresAdmissible evidence accepted
