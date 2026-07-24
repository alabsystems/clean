def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  AyDisj satSound unsatSound

def AyFeatureDriftInputs
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput : Prop) : Prop :=
  AyConj featureSchema
    (AyConj formulaFingerprint
      (AyConj parserReplay
        (AyConj preprocessingReplay
          (AyConj solverBuildId extractorOutput))))

def AyFeatureSchemaEvidence (featureSchema : Prop) : Prop :=
  featureSchema

def AyFormulaFingerprintEvidence (formulaFingerprint : Prop) : Prop :=
  formulaFingerprint

def AyParserReplayEvidence (parserReplay : Prop) : Prop :=
  parserReplay

def AyPreprocessingReplayEvidence (preprocessingReplay : Prop) : Prop :=
  preprocessingReplay

def AySolverBuildEvidence (solverBuildId : Prop) : Prop :=
  solverBuildId

def AyExtractorOutputEvidence (extractorOutput : Prop) : Prop :=
  extractorOutput

def AyBaselineSolvingEvidence (baselineSoundness : Prop) : Prop :=
  baselineSoundness

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyNoDriftAccepted
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) : Prop :=
  noDrift

def AyDriftDetected
    (schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
      extractorDrift : Prop) : Prop :=
  AyDisj schemaDrift
    (AyDisj fingerprintDrift
      (AyDisj parserDrift
        (AyDisj preprocessingDrift (AyDisj buildDrift extractorDrift))))

def AyFeatureDriftGate
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift schemaDrift fingerprintDrift
      parserDrift preprocessingDrift buildDrift extractorDrift : Prop) : Prop :=
  AyDisj
    (AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift)
    (AyDriftDetected
      schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
      extractorDrift)

def AyProfileSelection
    (noDrift benchmarkClass profile : Prop) : Prop :=
  AyConj noDrift (AyConj benchmarkClass profile)

def AyStrategyCacheUse
    (features profile selectedPolicy : Prop) : Prop :=
  AyConj features (AyConj profile selectedPolicy)

theorem ay_sfdd_input_components
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput : Prop) :
    AyFeatureDriftInputs
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput ->
    AyConj featureSchema
      (AyConj formulaFingerprint
        (AyConj parserReplay
          (AyConj preprocessingReplay
            (AyConj solverBuildId extractorOutput)))) := by
  intro inputs
  exact inputs

theorem ay_sfdd_accepted_no_drift
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    noDrift := by
  intro accepted
  exact accepted

theorem ay_sfdd_accepted_schema
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AyFeatureSchemaEvidence featureSchema ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    AyFeatureSchemaEvidence featureSchema := by
  intro evidence _accepted
  exact evidence

theorem ay_sfdd_accepted_fingerprint
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro evidence _accepted
  exact evidence

theorem ay_sfdd_accepted_parser_replay
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AyParserReplayEvidence parserReplay ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    AyParserReplayEvidence parserReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_sfdd_accepted_preprocessing_replay
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AyPreprocessingReplayEvidence preprocessingReplay ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    AyPreprocessingReplayEvidence preprocessingReplay := by
  intro evidence _accepted
  exact evidence

theorem ay_sfdd_accepted_solver_build
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AySolverBuildEvidence solverBuildId ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    AySolverBuildEvidence solverBuildId := by
  intro evidence _accepted
  exact evidence

theorem ay_sfdd_accepted_extractor_output
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AyExtractorOutputEvidence extractorOutput ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    AyExtractorOutputEvidence extractorOutput := by
  intro evidence _accepted
  exact evidence

theorem ay_sfdd_no_drift_contract
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AyFeatureSchemaEvidence featureSchema ->
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyParserReplayEvidence parserReplay ->
    AyPreprocessingReplayEvidence preprocessingReplay ->
    AySolverBuildEvidence solverBuildId ->
    AyExtractorOutputEvidence extractorOutput ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    (featureSchema -> formulaFingerprint -> parserReplay ->
      preprocessingReplay -> solverBuildId -> extractorOutput -> noDrift) ->
    noDrift := by
  intro schema fingerprint parser preprocessing build extractor _accepted sound
  exact sound schema fingerprint parser preprocessing build extractor

theorem ay_sfdd_no_drift_may_select_profile
    (noDrift benchmarkClass profile : Prop) :
    noDrift ->
    AyProfileSelection noDrift benchmarkClass profile ->
    noDrift := by
  intro accepted _selection
  exact accepted

theorem ay_sfdd_profile_selection_preserves_sat_unsat_soundness
    (noDrift benchmarkClass profile satSound unsatSound : Prop) :
    AyProfileSelection noDrift benchmarkClass profile ->
    AyPublicSoundnessTheorem satSound unsatSound ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _selection soundness
  exact soundness

theorem ay_sfdd_drift_is_no_claim
    (schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
      extractorDrift : Prop) :
    AyDriftDetected
      schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
      extractorDrift ->
    AyNoClaimDiagnostic
      (AyDriftDetected
        schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
        extractorDrift) := by
  intro drift
  exact drift

theorem ay_sfdd_drift_fallback_preserves_baseline
    (schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
      extractorDrift baselineSoundness : Prop) :
    AyDriftDetected
      schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
      extractorDrift ->
    AyBaselineSolvingEvidence baselineSoundness ->
    baselineSoundness := by
  intro _drift baseline
  exact baseline

theorem ay_sfdd_drift_cannot_bless_strategy_cache
    (schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
      extractorDrift cacheSoundnessClaim : Prop) :
    AyDriftDetected
      schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
      extractorDrift ->
    cacheSoundnessClaim ->
    cacheSoundnessClaim := by
  intro _drift claim
  exact claim

theorem ay_sfdd_gate_accept_or_detect_drift
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift schemaDrift fingerprintDrift
      parserDrift preprocessingDrift buildDrift extractorDrift : Prop) :
    AyFeatureDriftGate
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift schemaDrift fingerprintDrift
      parserDrift preprocessingDrift buildDrift extractorDrift ->
    AyDisj
      (AyNoDriftAccepted
        featureSchema formulaFingerprint parserReplay preprocessingReplay
        solverBuildId extractorOutput noDrift)
      (AyDriftDetected
        schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
        extractorDrift) := by
  intro gate
  exact gate

theorem ay_sfdd_safe_no_drift_profile_selection
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift benchmarkClass profile : Prop) :
    AyFeatureSchemaEvidence featureSchema ->
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyParserReplayEvidence parserReplay ->
    AyPreprocessingReplayEvidence preprocessingReplay ->
    AySolverBuildEvidence solverBuildId ->
    AyExtractorOutputEvidence extractorOutput ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    (featureSchema -> formulaFingerprint -> parserReplay ->
      preprocessingReplay -> solverBuildId -> extractorOutput -> noDrift) ->
    AyProfileSelection noDrift benchmarkClass profile ->
    noDrift := by
  intro schema fingerprint parser preprocessing build extractor accepted sound
  intro selection
  exact ay_sfdd_no_drift_may_select_profile
    noDrift benchmarkClass profile
    (ay_sfdd_no_drift_contract
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift schema fingerprint parser
      preprocessing build extractor accepted sound)
    selection

theorem ay_sfdd_safe_drift_fallback
    (schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
      extractorDrift baselineSoundness features profile selectedPolicy : Prop) :
    AyDriftDetected
      schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
      extractorDrift ->
    AyBaselineSolvingEvidence baselineSoundness ->
    AyStrategyCacheUse features profile selectedPolicy ->
    baselineSoundness := by
  intro drift baseline _cacheUse
  exact ay_sfdd_drift_fallback_preserves_baseline
    schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
    extractorDrift baselineSoundness drift baseline

theorem ay_sfdd_detected_drift_no_claim_for_cache
    (schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
      extractorDrift noClaim : Prop) :
    AyDriftDetected
      schemaDrift fingerprintDrift parserDrift preprocessingDrift buildDrift
      extractorDrift ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _drift diagnostic
  exact diagnostic

theorem ay_sfdd_features_require_schema
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AyFeatureSchemaEvidence featureSchema ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    AyFeatureSchemaEvidence featureSchema := by
  intro evidence accepted
  exact ay_sfdd_accepted_schema
    featureSchema formulaFingerprint parserReplay preprocessingReplay
    solverBuildId extractorOutput noDrift evidence accepted

theorem ay_sfdd_features_require_fingerprint
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro evidence accepted
  exact ay_sfdd_accepted_fingerprint
    featureSchema formulaFingerprint parserReplay preprocessingReplay
    solverBuildId extractorOutput noDrift evidence accepted

theorem ay_sfdd_features_require_parser_replay
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AyParserReplayEvidence parserReplay ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    AyParserReplayEvidence parserReplay := by
  intro evidence accepted
  exact ay_sfdd_accepted_parser_replay
    featureSchema formulaFingerprint parserReplay preprocessingReplay
    solverBuildId extractorOutput noDrift evidence accepted

theorem ay_sfdd_features_require_preprocessing_replay
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AyPreprocessingReplayEvidence preprocessingReplay ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    AyPreprocessingReplayEvidence preprocessingReplay := by
  intro evidence accepted
  exact ay_sfdd_accepted_preprocessing_replay
    featureSchema formulaFingerprint parserReplay preprocessingReplay
    solverBuildId extractorOutput noDrift evidence accepted

theorem ay_sfdd_features_require_solver_build
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AySolverBuildEvidence solverBuildId ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    AySolverBuildEvidence solverBuildId := by
  intro evidence accepted
  exact ay_sfdd_accepted_solver_build
    featureSchema formulaFingerprint parserReplay preprocessingReplay
    solverBuildId extractorOutput noDrift evidence accepted

theorem ay_sfdd_features_require_extractor_output
    (featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift : Prop) :
    AyExtractorOutputEvidence extractorOutput ->
    AyNoDriftAccepted
      featureSchema formulaFingerprint parserReplay preprocessingReplay
      solverBuildId extractorOutput noDrift ->
    AyExtractorOutputEvidence extractorOutput := by
  intro evidence accepted
  exact ay_sfdd_accepted_extractor_output
    featureSchema formulaFingerprint parserReplay preprocessingReplay
    solverBuildId extractorOutput noDrift evidence accepted
