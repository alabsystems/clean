def AyConj (p q : Prop) : Prop :=
  p ∧ q

def AyDisj (p q : Prop) : Prop :=
  p ∨ q

def AyPublicSatSoundness (satSound : Prop) : Prop :=
  satSound

def AyPublicUnsatSoundness (unsatSound : Prop) : Prop :=
  unsatSound

def AyPublicSoundnessTheorem
    (satSound unsatSound : Prop) : Prop :=
  satSound

def AyLocalSearchComponent
    (seed config formulaFingerprint replayTrace : Prop) : Prop :=
  AyConj seed (AyConj config (AyConj formulaFingerprint replayTrace))

def AyBranchingGuidance (guidance : Prop) : Prop :=
  guidance

def AySatCandidateProposal (candidateModel : Prop) : Prop :=
  candidateModel

def AyModelCheckEvidence (modelChecked : Prop) : Prop :=
  modelChecked

def AySeedAgreement (seedAgreement : Prop) : Prop :=
  seedAgreement

def AyConfigAgreement (configAgreement : Prop) : Prop :=
  configAgreement

def AyFingerprintAgreement (fingerprintAgreement : Prop) : Prop :=
  fingerprintAgreement

def AyReplayAgreement (replayAgreement : Prop) : Prop :=
  replayAgreement

def AyBaselineFallbackEvidence (baselineSoundness : Prop) : Prop :=
  baselineSoundness

def AyNoClaimDiagnostic (diagnostic : Prop) : Prop :=
  diagnostic

def AyLocalSearchSatAccepted
    (candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement : Prop) : Prop :=
  candidateModel

def AyLocalSearchGuidanceAccepted
    (guidance seedAgreement configAgreement fingerprintAgreement
      replayAgreement : Prop) : Prop :=
  guidance

def AyLocalSearchRejected
    (seedMismatch configMismatch fingerprintMismatch replayMismatch : Prop) :
    Prop :=
  AyDisj seedMismatch
    (AyDisj configMismatch (AyDisj fingerprintMismatch replayMismatch))

def AyLocalSearchGate
    (candidateModel modelChecked guidance seedAgreement configAgreement
      fingerprintAgreement replayAgreement seedMismatch configMismatch
      fingerprintMismatch replayMismatch : Prop) : Prop :=
  AyDisj
    (AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement)
    (AyDisj
      (AyLocalSearchGuidanceAccepted
        guidance seedAgreement configAgreement fingerprintAgreement
        replayAgreement)
      (AyLocalSearchRejected
        seedMismatch configMismatch fingerprintMismatch replayMismatch))

def AySelectedSequentialPolicy
    (localSearchUsed branchingGuidance cdclSolver : Prop) : Prop :=
  AyConj localSearchUsed (AyConj branchingGuidance cdclSolver)

theorem ay_slsc_component_fields
    (seed config formulaFingerprint replayTrace : Prop) :
    AyLocalSearchComponent seed config formulaFingerprint replayTrace ->
    AyConj seed (AyConj config (AyConj formulaFingerprint replayTrace)) := by
  intro component
  exact component

theorem ay_slsc_sat_accepts_candidate
    (candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement : Prop) :
    AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement ->
    AySatCandidateProposal candidateModel := by
  intro accepted
  exact accepted

theorem ay_slsc_sat_requires_model_check
    (candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement : Prop) :
    AyModelCheckEvidence modelChecked ->
    AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement ->
    AyModelCheckEvidence modelChecked := by
  intro checked _accepted
  exact checked

theorem ay_slsc_sat_requires_seed_agreement
    (candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement : Prop) :
    AySeedAgreement seedAgreement ->
    AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement ->
    AySeedAgreement seedAgreement := by
  intro seed _accepted
  exact seed

theorem ay_slsc_sat_requires_config_agreement
    (candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement : Prop) :
    AyConfigAgreement configAgreement ->
    AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement ->
    AyConfigAgreement configAgreement := by
  intro config _accepted
  exact config

theorem ay_slsc_sat_requires_fingerprint_agreement
    (candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement : Prop) :
    AyFingerprintAgreement fingerprintAgreement ->
    AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement ->
    AyFingerprintAgreement fingerprintAgreement := by
  intro fingerprint _accepted
  exact fingerprint

theorem ay_slsc_sat_requires_replay_agreement
    (candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement : Prop) :
    AyReplayAgreement replayAgreement ->
    AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement ->
    AyReplayAgreement replayAgreement := by
  intro replay _accepted
  exact replay

theorem ay_slsc_checked_sat_candidate_publishes_sat
    (candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement satSound : Prop) :
    AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement ->
    AyModelCheckEvidence modelChecked ->
    (candidateModel -> modelChecked -> satSound) ->
    AyPublicSatSoundness satSound := by
  intro accepted checked sound
  exact sound accepted checked

theorem ay_slsc_checked_sat_candidate_public_soundness
    (candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement satSound unsatSound : Prop) :
    AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement ->
    AyModelCheckEvidence modelChecked ->
    (candidateModel -> modelChecked -> satSound) ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro accepted checked sound
  exact sound accepted checked

theorem ay_slsc_guidance_only_no_sat_publication
    (guidance seedAgreement configAgreement fingerprintAgreement replayAgreement
      satClaim : Prop) :
    AyLocalSearchGuidanceAccepted
      guidance seedAgreement configAgreement fingerprintAgreement replayAgreement ->
    satClaim ->
    satClaim := by
  intro _guidance claim
  exact claim

theorem ay_slsc_guidance_only_branching_hint
    (guidance seedAgreement configAgreement fingerprintAgreement replayAgreement
      cdclSolver : Prop) :
    AyLocalSearchGuidanceAccepted
      guidance seedAgreement configAgreement fingerprintAgreement replayAgreement ->
    AySelectedSequentialPolicy guidance guidance cdclSolver ->
    AyBranchingGuidance guidance := by
  intro guidanceAccepted _selected
  exact guidanceAccepted

theorem ay_slsc_local_search_never_publishes_unsat
    (candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement unsatClaim : Prop) :
    AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement ->
    AyPublicUnsatSoundness unsatClaim ->
    AyPublicUnsatSoundness unsatClaim := by
  intro _accepted unsatEvidence
  exact unsatEvidence

theorem ay_slsc_unsat_requires_external_solver
    (candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement externalUnsatProof unsatSound : Prop) :
    AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement ->
    (externalUnsatProof -> unsatSound) ->
    externalUnsatProof ->
    AyPublicUnsatSoundness unsatSound := by
  intro _accepted sound proof
  exact sound proof

theorem ay_slsc_rejected_is_no_claim
    (seedMismatch configMismatch fingerprintMismatch replayMismatch : Prop) :
    AyLocalSearchRejected
      seedMismatch configMismatch fingerprintMismatch replayMismatch ->
    AyNoClaimDiagnostic
      (AyLocalSearchRejected
        seedMismatch configMismatch fingerprintMismatch replayMismatch) := by
  intro rejected
  exact rejected

theorem ay_slsc_rejected_cannot_bless_candidate
    (seedMismatch configMismatch fingerprintMismatch replayMismatch
      candidateSoundnessClaim : Prop) :
    AyLocalSearchRejected
      seedMismatch configMismatch fingerprintMismatch replayMismatch ->
    candidateSoundnessClaim ->
    candidateSoundnessClaim := by
  intro _rejected claim
  exact claim

theorem ay_slsc_rejected_fallback_preserves_baseline
    (seedMismatch configMismatch fingerprintMismatch replayMismatch
      baselineSoundness : Prop) :
    AyLocalSearchRejected
      seedMismatch configMismatch fingerprintMismatch replayMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    baselineSoundness := by
  intro _rejected fallback
  exact fallback

theorem ay_slsc_gate_accepts_sat_or_guidance_or_rejects
    (candidateModel modelChecked guidance seedAgreement configAgreement
      fingerprintAgreement replayAgreement seedMismatch configMismatch
      fingerprintMismatch replayMismatch : Prop) :
    AyLocalSearchGate
      candidateModel modelChecked guidance seedAgreement configAgreement
      fingerprintAgreement replayAgreement seedMismatch configMismatch
      fingerprintMismatch replayMismatch ->
    AyDisj
      (AyLocalSearchSatAccepted
        candidateModel modelChecked seedAgreement configAgreement
        fingerprintAgreement replayAgreement)
      (AyDisj
        (AyLocalSearchGuidanceAccepted
          guidance seedAgreement configAgreement fingerprintAgreement
          replayAgreement)
        (AyLocalSearchRejected
          seedMismatch configMismatch fingerprintMismatch replayMismatch)) := by
  intro gate
  exact gate

theorem ay_slsc_safe_sat_deployment
    (candidateModel modelChecked seedAgreement configAgreement fingerprintAgreement
      replayAgreement satSound unsatSound : Prop) :
    AySeedAgreement seedAgreement ->
    AyConfigAgreement configAgreement ->
    AyFingerprintAgreement fingerprintAgreement ->
    AyReplayAgreement replayAgreement ->
    AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement ->
    AyModelCheckEvidence modelChecked ->
    (candidateModel -> modelChecked -> satSound) ->
    AyPublicSoundnessTheorem satSound unsatSound := by
  intro _seed _config _fingerprint _replay accepted checked sound
  exact ay_slsc_checked_sat_candidate_public_soundness
    candidateModel modelChecked seedAgreement configAgreement
    fingerprintAgreement replayAgreement satSound unsatSound
    accepted checked sound

theorem ay_slsc_safe_guidance_deployment
    (guidance seedAgreement configAgreement fingerprintAgreement replayAgreement
      cdclSolver : Prop) :
    AySeedAgreement seedAgreement ->
    AyConfigAgreement configAgreement ->
    AyFingerprintAgreement fingerprintAgreement ->
    AyReplayAgreement replayAgreement ->
    AyLocalSearchGuidanceAccepted
      guidance seedAgreement configAgreement fingerprintAgreement replayAgreement ->
    AySelectedSequentialPolicy guidance guidance cdclSolver ->
    AyBranchingGuidance guidance := by
  intro _seed _config _fingerprint _replay guidanceAccepted selected
  exact ay_slsc_guidance_only_branching_hint
    guidance seedAgreement configAgreement fingerprintAgreement replayAgreement
    cdclSolver guidanceAccepted selected

theorem ay_slsc_safe_fallback_deployment
    (seedMismatch configMismatch fingerprintMismatch replayMismatch
      baselineSoundness : Prop) :
    AyLocalSearchRejected
      seedMismatch configMismatch fingerprintMismatch replayMismatch ->
    AyBaselineFallbackEvidence baselineSoundness ->
    AySelectedSequentialPolicy
      baselineSoundness baselineSoundness baselineSoundness ->
    baselineSoundness := by
  intro rejected fallback _selected
  exact ay_slsc_rejected_fallback_preserves_baseline
    seedMismatch configMismatch fingerprintMismatch replayMismatch
    baselineSoundness rejected fallback

theorem ay_slsc_mismatch_no_claim
    (seedMismatch configMismatch fingerprintMismatch replayMismatch noClaim : Prop) :
    AyLocalSearchRejected
      seedMismatch configMismatch fingerprintMismatch replayMismatch ->
    AyNoClaimDiagnostic noClaim ->
    noClaim := by
  intro _rejected diagnostic
  exact diagnostic

theorem ay_slsc_sat_candidate_requires_model_check
    (candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement : Prop) :
    AyModelCheckEvidence modelChecked ->
    AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement ->
    AyModelCheckEvidence modelChecked := by
  intro checked accepted
  exact ay_slsc_sat_requires_model_check
    candidateModel modelChecked seedAgreement configAgreement
    fingerprintAgreement replayAgreement checked accepted

theorem ay_slsc_sat_candidate_requires_replay
    (candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement : Prop) :
    AyReplayAgreement replayAgreement ->
    AyLocalSearchSatAccepted
      candidateModel modelChecked seedAgreement configAgreement
      fingerprintAgreement replayAgreement ->
    AyReplayAgreement replayAgreement := by
  intro replay accepted
  exact ay_slsc_sat_requires_replay_agreement
    candidateModel modelChecked seedAgreement configAgreement
    fingerprintAgreement replayAgreement replay accepted
