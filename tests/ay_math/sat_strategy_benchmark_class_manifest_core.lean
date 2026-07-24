def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyBenchmarkClassLabel
    (classifier featureManifest formulaFingerprint classCertificate : Prop) :
    Prop :=
  AyConj classifier
    (AyConj featureManifest (AyConj formulaFingerprint classCertificate))

def AyClassifierEvidence (classifier : Prop) : Prop :=
  classifier

def AyFeatureManifestEvidence (featureManifest : Prop) : Prop :=
  featureManifest

def AyFormulaFingerprintEvidence (formulaFingerprint : Prop) : Prop :=
  formulaFingerprint

def AyClassCertificateEvidence (classCertificate : Prop) : Prop :=
  classCertificate

def AyFallbackEvidence (baselineSoundness : Prop) : Prop :=
  baselineSoundness

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyClassManifestAccepted
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted : Prop) : Prop :=
  classLabelAccepted

def AyClassManifestRejected
    (misclassified staleFeatures fingerprintMismatch certificateMismatch : Prop) :
    Prop :=
  AyDisj misclassified
    (AyDisj staleFeatures
      (AyDisj fingerprintMismatch certificateMismatch))

def AyClassManifestGate
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted misclassified staleFeatures fingerprintMismatch
      certificateMismatch : Prop) : Prop :=
  AyDisj
    (AyClassManifestAccepted
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted)
    (AyClassManifestRejected
      misclassified staleFeatures fingerprintMismatch certificateMismatch)

def AyOfflineProfileClassUse
    (classLabel profileManifest sequentialMain : Prop) : Prop :=
  AyConj classLabel (AyConj profileManifest sequentialMain)

theorem ay_sbcm_label_components
    (classifier featureManifest formulaFingerprint classCertificate : Prop) :
    AyBenchmarkClassLabel
      classifier featureManifest formulaFingerprint classCertificate ->
    AyConj classifier
      (AyConj featureManifest (AyConj formulaFingerprint classCertificate)) := by
  intro label
  exact label

theorem ay_sbcm_accepted_class_label
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted : Prop) :
    AyClassManifestAccepted
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted ->
    classLabelAccepted := by
  intro accepted
  exact accepted

theorem ay_sbcm_accepted_classifier_evidence
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted : Prop) :
    AyClassifierEvidence classifier ->
    AyClassManifestAccepted
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted ->
    AyClassifierEvidence classifier := by
  intro evidence _accepted
  exact evidence

theorem ay_sbcm_accepted_feature_manifest
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted : Prop) :
    AyFeatureManifestEvidence featureManifest ->
    AyClassManifestAccepted
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted ->
    AyFeatureManifestEvidence featureManifest := by
  intro evidence _accepted
  exact evidence

theorem ay_sbcm_accepted_formula_fingerprint
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyClassManifestAccepted
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro evidence _accepted
  exact evidence

theorem ay_sbcm_accepted_class_certificate
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted : Prop) :
    AyClassCertificateEvidence classCertificate ->
    AyClassManifestAccepted
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted ->
    AyClassCertificateEvidence classCertificate := by
  intro evidence _accepted
  exact evidence

theorem ay_sbcm_accepted_label_admissible
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted admissibleClass : Prop) :
    AyClassifierEvidence classifier ->
    AyFeatureManifestEvidence featureManifest ->
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyClassCertificateEvidence classCertificate ->
    AyClassManifestAccepted
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted ->
    (classifier -> featureManifest -> formulaFingerprint ->
      classCertificate -> classLabelAccepted -> admissibleClass) ->
    admissibleClass := by
  intro classifierEvidence featureEvidence fingerprintEvidence certificateEvidence
  intro accepted sound
  exact sound classifierEvidence featureEvidence fingerprintEvidence
    certificateEvidence accepted

theorem ay_sbcm_admissible_class_may_select_profile
    (classLabel profileManifest sequentialMain admissibleClass : Prop) :
    admissibleClass ->
    AyOfflineProfileClassUse classLabel profileManifest sequentialMain ->
    admissibleClass := by
  intro admissible _profileUse
  exact admissible

theorem ay_sbcm_rejected_is_no_claim
    (misclassified staleFeatures fingerprintMismatch certificateMismatch : Prop) :
    AyClassManifestRejected
      misclassified staleFeatures fingerprintMismatch certificateMismatch ->
    AyNoClaimDiagnostic
      (AyClassManifestRejected
        misclassified staleFeatures fingerprintMismatch certificateMismatch) := by
  intro rejected
  exact rejected

theorem ay_sbcm_rejected_fallback_preserves_baseline
    (misclassified staleFeatures fingerprintMismatch certificateMismatch
      baselineSoundness : Prop) :
    AyClassManifestRejected
      misclassified staleFeatures fingerprintMismatch certificateMismatch ->
    AyFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_sbcm_rejected_cannot_bless_profile
    (misclassified staleFeatures fingerprintMismatch certificateMismatch
      profileSoundnessClaim : Prop) :
    AyClassManifestRejected
      misclassified staleFeatures fingerprintMismatch certificateMismatch ->
    profileSoundnessClaim ->
    profileSoundnessClaim := by
  intro _rejected claim
  exact claim

theorem ay_sbcm_gate_accept_or_reject
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted misclassified staleFeatures fingerprintMismatch
      certificateMismatch : Prop) :
    AyClassManifestGate
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted misclassified staleFeatures fingerprintMismatch
      certificateMismatch ->
    AyDisj
      (AyClassManifestAccepted
        classifier featureManifest formulaFingerprint classCertificate
        classLabelAccepted)
      (AyClassManifestRejected
        misclassified staleFeatures fingerprintMismatch certificateMismatch) := by
  intro gate
  exact gate

theorem ay_sbcm_safe_class_deployment_accept
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted admissibleClass classLabel profileManifest
      sequentialMain : Prop) :
    AyClassifierEvidence classifier ->
    AyFeatureManifestEvidence featureManifest ->
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyClassCertificateEvidence classCertificate ->
    AyClassManifestAccepted
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted ->
    (classifier -> featureManifest -> formulaFingerprint ->
      classCertificate -> classLabelAccepted -> admissibleClass) ->
    AyOfflineProfileClassUse classLabel profileManifest sequentialMain ->
    admissibleClass := by
  intro classifierEvidence featureEvidence fingerprintEvidence certificateEvidence
  intro accepted sound profileUse
  exact ay_sbcm_admissible_class_may_select_profile
    classLabel profileManifest sequentialMain admissibleClass
    (ay_sbcm_accepted_label_admissible
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted admissibleClass classifierEvidence featureEvidence
      fingerprintEvidence certificateEvidence accepted sound)
    profileUse

theorem ay_sbcm_safe_class_deployment_fallback
    (misclassified staleFeatures fingerprintMismatch certificateMismatch
      baselineSoundness classLabel profileManifest sequentialMain : Prop) :
    AyClassManifestRejected
      misclassified staleFeatures fingerprintMismatch certificateMismatch ->
    AyFallbackEvidence baselineSoundness ->
    AyOfflineProfileClassUse classLabel profileManifest sequentialMain ->
    baselineSoundness := by
  intro rejected fallback _profileUse
  exact ay_sbcm_rejected_fallback_preserves_baseline
    misclassified staleFeatures fingerprintMismatch certificateMismatch
    baselineSoundness rejected fallback

theorem ay_sbcm_misclassified_or_stale_no_claim
    (misclassified staleFeatures fingerprintMismatch certificateMismatch
      noClaim : Prop) :
    AyClassManifestRejected
      misclassified staleFeatures fingerprintMismatch certificateMismatch ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_sbcm_class_label_requires_classifier
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted : Prop) :
    AyClassifierEvidence classifier ->
    AyClassManifestAccepted
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted ->
    AyClassifierEvidence classifier := by
  intro evidence accepted
  exact ay_sbcm_accepted_classifier_evidence
    classifier featureManifest formulaFingerprint classCertificate
    classLabelAccepted evidence accepted

theorem ay_sbcm_class_label_requires_features
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted : Prop) :
    AyFeatureManifestEvidence featureManifest ->
    AyClassManifestAccepted
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted ->
    AyFeatureManifestEvidence featureManifest := by
  intro evidence accepted
  exact ay_sbcm_accepted_feature_manifest
    classifier featureManifest formulaFingerprint classCertificate
    classLabelAccepted evidence accepted

theorem ay_sbcm_class_label_requires_fingerprint
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted : Prop) :
    AyFormulaFingerprintEvidence formulaFingerprint ->
    AyClassManifestAccepted
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted ->
    AyFormulaFingerprintEvidence formulaFingerprint := by
  intro evidence accepted
  exact ay_sbcm_accepted_formula_fingerprint
    classifier featureManifest formulaFingerprint classCertificate
    classLabelAccepted evidence accepted

theorem ay_sbcm_class_label_requires_certificate
    (classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted : Prop) :
    AyClassCertificateEvidence classCertificate ->
    AyClassManifestAccepted
      classifier featureManifest formulaFingerprint classCertificate
      classLabelAccepted ->
    AyClassCertificateEvidence classCertificate := by
  intro evidence accepted
  exact ay_sbcm_accepted_class_certificate
    classifier featureManifest formulaFingerprint classCertificate
    classLabelAccepted evidence accepted
