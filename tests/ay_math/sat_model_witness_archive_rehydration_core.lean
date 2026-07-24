-- SAT-COMP/ay SAT witness archive rehydration soundness skeleton.
-- A compact archived witness may validate SAT publication only when archive
-- membership, digest, variable maps, eliminated defaults, projection evidence,
-- checker replay, and original formula fingerprint evidence all agree.

def AyMWARConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMWARDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMWAREquisat (left right : Prop) : Prop :=
  AyMWARConj (left -> right) (right -> left)

def AyMWARArchiveMembership
    (archiveRoot witnessEntry entryIncluded : Prop) : Prop :=
  AyMWARConj archiveRoot (AyMWARConj witnessEntry entryIncluded)

def AyMWARWitnessDigest
    (compactWitness witnessDigest digestAgreement : Prop) : Prop :=
  AyMWARConj compactWitness (AyMWARConj witnessDigest digestAgreement)

def AyMWARVariableMap
    (compactVariableMap originalVariableMap mapAgreement : Prop) : Prop :=
  AyMWARConj compactVariableMap
    (AyMWARConj originalVariableMap mapAgreement)

def AyMWAREliminatedDefaults
    (eliminatedVariables defaultAssignments defaultsComplete : Prop) : Prop :=
  AyMWARConj eliminatedVariables
    (AyMWARConj defaultAssignments defaultsComplete)

def AyMWARProjectionReconstruction
    (projectionEvidence reconstructionEvidence witnessComplete : Prop) :
    Prop :=
  AyMWARConj projectionEvidence
    (AyMWARConj reconstructionEvidence witnessComplete)

def AyMWARModelCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMWARConj checkerAccepted replayTrace

def AyMWAROriginalFormulaFingerprint
    (formulaFingerprint archivedFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMWARConj formulaFingerprint
    (AyMWARConj archivedFingerprint fingerprintAgreement)

def AyMWARRehydrationEvidence
    (membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk : Prop) : Prop :=
  AyMWARConj membershipOk
    (AyMWARConj digestOk
      (AyMWARConj mapOk
        (AyMWARConj defaultsOk
          (AyMWARConj projectionOk
            (AyMWARConj checkerOk fingerprintOk)))))

def AyMWARRehydratedSatValidation
    (rehydrationEvidence auditEntry publicSatModel : Prop) : Prop :=
  AyMWARConj rehydrationEvidence
    (AyMWARConj auditEntry publicSatModel)

def AyMWARNoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMWARConj diagnostic (publicClaim -> False)

def AyMWARRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMWARConj reason recomputeRequest

theorem ay_mwar_conj_intro {left right : Prop} :
    left -> right -> AyMWARConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mwar_conj_left {left right : Prop} :
    AyMWARConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mwar_conj_right {left right : Prop} :
    AyMWARConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mwar_disj_left {left right : Prop} :
    left -> AyMWARDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mwar_disj_right {left right : Prop} :
    right -> AyMWARDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mwar_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMWAREquisat left right :=
  fun hf hb => ay_mwar_conj_intro hf hb

theorem ay_mwar_equisat_forward {left right : Prop} :
    AyMWAREquisat left right -> left -> right :=
  fun h => ay_mwar_conj_left h

theorem ay_mwar_equisat_backward {left right : Prop} :
    AyMWAREquisat left right -> right -> left :=
  fun h => ay_mwar_conj_right h

theorem ay_mwar_archive_membership_intro
    {archiveRoot witnessEntry entryIncluded : Prop} :
    archiveRoot ->
    witnessEntry ->
    entryIncluded ->
    AyMWARArchiveMembership archiveRoot witnessEntry entryIncluded :=
  fun hroot hentry hincluded =>
    ay_mwar_conj_intro hroot (ay_mwar_conj_intro hentry hincluded)

theorem ay_mwar_archive_membership_root
    {archiveRoot witnessEntry entryIncluded : Prop} :
    AyMWARArchiveMembership archiveRoot witnessEntry entryIncluded ->
    archiveRoot :=
  fun h => ay_mwar_conj_left h

theorem ay_mwar_archive_membership_entry
    {archiveRoot witnessEntry entryIncluded : Prop} :
    AyMWARArchiveMembership archiveRoot witnessEntry entryIncluded ->
    witnessEntry :=
  fun h => ay_mwar_conj_left (ay_mwar_conj_right h)

theorem ay_mwar_archive_membership_included
    {archiveRoot witnessEntry entryIncluded : Prop} :
    AyMWARArchiveMembership archiveRoot witnessEntry entryIncluded ->
    entryIncluded :=
  fun h => ay_mwar_conj_right (ay_mwar_conj_right h)

theorem ay_mwar_witness_digest_intro
    {compactWitness witnessDigest digestAgreement : Prop} :
    compactWitness ->
    witnessDigest ->
    digestAgreement ->
    AyMWARWitnessDigest compactWitness witnessDigest digestAgreement :=
  fun hwitness hdigest hagree =>
    ay_mwar_conj_intro hwitness (ay_mwar_conj_intro hdigest hagree)

theorem ay_mwar_witness_digest_witness
    {compactWitness witnessDigest digestAgreement : Prop} :
    AyMWARWitnessDigest compactWitness witnessDigest digestAgreement ->
    compactWitness :=
  fun h => ay_mwar_conj_left h

theorem ay_mwar_witness_digest_digest
    {compactWitness witnessDigest digestAgreement : Prop} :
    AyMWARWitnessDigest compactWitness witnessDigest digestAgreement ->
    witnessDigest :=
  fun h => ay_mwar_conj_left (ay_mwar_conj_right h)

theorem ay_mwar_witness_digest_agreement
    {compactWitness witnessDigest digestAgreement : Prop} :
    AyMWARWitnessDigest compactWitness witnessDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mwar_conj_right (ay_mwar_conj_right h)

theorem ay_mwar_variable_map_intro
    {compactVariableMap originalVariableMap mapAgreement : Prop} :
    compactVariableMap ->
    originalVariableMap ->
    mapAgreement ->
    AyMWARVariableMap compactVariableMap originalVariableMap mapAgreement :=
  fun hcompact horiginal hagree =>
    ay_mwar_conj_intro hcompact (ay_mwar_conj_intro horiginal hagree)

theorem ay_mwar_variable_map_compact
    {compactVariableMap originalVariableMap mapAgreement : Prop} :
    AyMWARVariableMap compactVariableMap originalVariableMap mapAgreement ->
    compactVariableMap :=
  fun h => ay_mwar_conj_left h

theorem ay_mwar_variable_map_original
    {compactVariableMap originalVariableMap mapAgreement : Prop} :
    AyMWARVariableMap compactVariableMap originalVariableMap mapAgreement ->
    originalVariableMap :=
  fun h => ay_mwar_conj_left (ay_mwar_conj_right h)

theorem ay_mwar_variable_map_agreement
    {compactVariableMap originalVariableMap mapAgreement : Prop} :
    AyMWARVariableMap compactVariableMap originalVariableMap mapAgreement ->
    mapAgreement :=
  fun h => ay_mwar_conj_right (ay_mwar_conj_right h)

theorem ay_mwar_eliminated_defaults_intro
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    eliminatedVariables ->
    defaultAssignments ->
    defaultsComplete ->
    AyMWAREliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete :=
  fun helim hdefaults hcomplete =>
    ay_mwar_conj_intro helim
      (ay_mwar_conj_intro hdefaults hcomplete)

theorem ay_mwar_eliminated_defaults_variables
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMWAREliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    eliminatedVariables :=
  fun h => ay_mwar_conj_left h

theorem ay_mwar_eliminated_defaults_assignments
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMWAREliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    defaultAssignments :=
  fun h => ay_mwar_conj_left (ay_mwar_conj_right h)

theorem ay_mwar_eliminated_defaults_complete
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMWAREliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    defaultsComplete :=
  fun h => ay_mwar_conj_right (ay_mwar_conj_right h)

theorem ay_mwar_projection_reconstruction_intro
    {projectionEvidence reconstructionEvidence witnessComplete : Prop} :
    projectionEvidence ->
    reconstructionEvidence ->
    witnessComplete ->
    AyMWARProjectionReconstruction
      projectionEvidence reconstructionEvidence witnessComplete :=
  fun hprojection hreconstruction hcomplete =>
    ay_mwar_conj_intro hprojection
      (ay_mwar_conj_intro hreconstruction hcomplete)

theorem ay_mwar_projection_reconstruction_projection
    {projectionEvidence reconstructionEvidence witnessComplete : Prop} :
    AyMWARProjectionReconstruction
      projectionEvidence reconstructionEvidence witnessComplete ->
    projectionEvidence :=
  fun h => ay_mwar_conj_left h

theorem ay_mwar_projection_reconstruction_reconstruction
    {projectionEvidence reconstructionEvidence witnessComplete : Prop} :
    AyMWARProjectionReconstruction
      projectionEvidence reconstructionEvidence witnessComplete ->
    reconstructionEvidence :=
  fun h => ay_mwar_conj_left (ay_mwar_conj_right h)

theorem ay_mwar_projection_reconstruction_complete
    {projectionEvidence reconstructionEvidence witnessComplete : Prop} :
    AyMWARProjectionReconstruction
      projectionEvidence reconstructionEvidence witnessComplete ->
    witnessComplete :=
  fun h => ay_mwar_conj_right (ay_mwar_conj_right h)

theorem ay_mwar_model_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMWARModelCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mwar_conj_intro haccepted htrace

theorem ay_mwar_model_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMWARModelCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_mwar_conj_left h

theorem ay_mwar_model_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMWARModelCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_mwar_conj_right h

theorem ay_mwar_original_formula_fingerprint_intro
    {formulaFingerprint archivedFingerprint fingerprintAgreement : Prop} :
    formulaFingerprint ->
    archivedFingerprint ->
    fingerprintAgreement ->
    AyMWAROriginalFormulaFingerprint
      formulaFingerprint archivedFingerprint fingerprintAgreement :=
  fun hformula harchived hagree =>
    ay_mwar_conj_intro hformula
      (ay_mwar_conj_intro harchived hagree)

theorem ay_mwar_original_formula_fingerprint_formula
    {formulaFingerprint archivedFingerprint fingerprintAgreement : Prop} :
    AyMWAROriginalFormulaFingerprint
      formulaFingerprint archivedFingerprint fingerprintAgreement ->
    formulaFingerprint :=
  fun h => ay_mwar_conj_left h

theorem ay_mwar_original_formula_fingerprint_archived
    {formulaFingerprint archivedFingerprint fingerprintAgreement : Prop} :
    AyMWAROriginalFormulaFingerprint
      formulaFingerprint archivedFingerprint fingerprintAgreement ->
    archivedFingerprint :=
  fun h => ay_mwar_conj_left (ay_mwar_conj_right h)

theorem ay_mwar_original_formula_fingerprint_agreement
    {formulaFingerprint archivedFingerprint fingerprintAgreement : Prop} :
    AyMWAROriginalFormulaFingerprint
      formulaFingerprint archivedFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mwar_conj_right (ay_mwar_conj_right h)

theorem ay_mwar_rehydration_evidence_intro
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk : Prop} :
    membershipOk ->
    digestOk ->
    mapOk ->
    defaultsOk ->
    projectionOk ->
    checkerOk ->
    fingerprintOk ->
    AyMWARRehydrationEvidence
      membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk :=
  fun hmembership hdigest hmap hdefaults hprojection hchecker hfingerprint =>
    ay_mwar_conj_intro hmembership
      (ay_mwar_conj_intro hdigest
        (ay_mwar_conj_intro hmap
          (ay_mwar_conj_intro hdefaults
            (ay_mwar_conj_intro hprojection
              (ay_mwar_conj_intro hchecker hfingerprint)))))

theorem ay_mwar_rehydration_evidence_membership
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk : Prop} :
    AyMWARRehydrationEvidence
      membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk ->
    membershipOk :=
  fun h => ay_mwar_conj_left h

theorem ay_mwar_rehydration_evidence_digest
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk : Prop} :
    AyMWARRehydrationEvidence
      membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk ->
    digestOk :=
  fun h => ay_mwar_conj_left (ay_mwar_conj_right h)

theorem ay_mwar_rehydration_evidence_map
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk : Prop} :
    AyMWARRehydrationEvidence
      membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk ->
    mapOk :=
  fun h => ay_mwar_conj_left (ay_mwar_conj_right (ay_mwar_conj_right h))

theorem ay_mwar_rehydration_evidence_defaults
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk : Prop} :
    AyMWARRehydrationEvidence
      membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk ->
    defaultsOk :=
  fun h =>
    ay_mwar_conj_left
      (ay_mwar_conj_right (ay_mwar_conj_right (ay_mwar_conj_right h)))

theorem ay_mwar_rehydration_evidence_projection
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk : Prop} :
    AyMWARRehydrationEvidence
      membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk ->
    projectionOk :=
  fun h =>
    ay_mwar_conj_left
      (ay_mwar_conj_right
        (ay_mwar_conj_right (ay_mwar_conj_right (ay_mwar_conj_right h))))

theorem ay_mwar_rehydration_evidence_checker
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk : Prop} :
    AyMWARRehydrationEvidence
      membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk ->
    checkerOk :=
  fun h =>
    ay_mwar_conj_left
      (ay_mwar_conj_right
        (ay_mwar_conj_right
          (ay_mwar_conj_right (ay_mwar_conj_right (ay_mwar_conj_right h)))))

theorem ay_mwar_rehydration_evidence_fingerprint
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk : Prop} :
    AyMWARRehydrationEvidence
      membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk ->
    fingerprintOk :=
  fun h =>
    ay_mwar_conj_right
      (ay_mwar_conj_right
        (ay_mwar_conj_right
          (ay_mwar_conj_right (ay_mwar_conj_right (ay_mwar_conj_right h)))))

theorem ay_mwar_rehydrated_sat_validation_intro
    {rehydrationEvidence auditEntry publicSatModel : Prop} :
    rehydrationEvidence ->
    auditEntry ->
    publicSatModel ->
    AyMWARRehydratedSatValidation
      rehydrationEvidence auditEntry publicSatModel :=
  fun hevidence haudit hmodel =>
    ay_mwar_conj_intro hevidence (ay_mwar_conj_intro haudit hmodel)

theorem ay_mwar_rehydrated_sat_validation_evidence
    {rehydrationEvidence auditEntry publicSatModel : Prop} :
    AyMWARRehydratedSatValidation
      rehydrationEvidence auditEntry publicSatModel ->
    rehydrationEvidence :=
  fun h => ay_mwar_conj_left h

theorem ay_mwar_rehydrated_sat_validation_audit
    {rehydrationEvidence auditEntry publicSatModel : Prop} :
    AyMWARRehydratedSatValidation
      rehydrationEvidence auditEntry publicSatModel ->
    auditEntry :=
  fun h => ay_mwar_conj_left (ay_mwar_conj_right h)

theorem ay_mwar_rehydrated_sat_validation_model
    {rehydrationEvidence auditEntry publicSatModel : Prop} :
    AyMWARRehydratedSatValidation
      rehydrationEvidence auditEntry publicSatModel ->
    publicSatModel :=
  fun h => ay_mwar_conj_right (ay_mwar_conj_right h)

theorem ay_mwar_accepted_rehydration_validates_sat_publication
    {rehydrationEvidence auditEntry publicSatModel : Prop} :
    AyMWARRehydratedSatValidation
      rehydrationEvidence auditEntry publicSatModel ->
    publicSatModel :=
  fun h => ay_mwar_rehydrated_sat_validation_model h

theorem ay_mwar_validation_requires_membership
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMWARRehydratedSatValidation
      (AyMWARRehydrationEvidence
        membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    membershipOk :=
  fun h =>
    ay_mwar_rehydration_evidence_membership
      (ay_mwar_rehydrated_sat_validation_evidence h)

theorem ay_mwar_validation_requires_digest
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMWARRehydratedSatValidation
      (AyMWARRehydrationEvidence
        membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    digestOk :=
  fun h =>
    ay_mwar_rehydration_evidence_digest
      (ay_mwar_rehydrated_sat_validation_evidence h)

theorem ay_mwar_validation_requires_map
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMWARRehydratedSatValidation
      (AyMWARRehydrationEvidence
        membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    mapOk :=
  fun h =>
    ay_mwar_rehydration_evidence_map
      (ay_mwar_rehydrated_sat_validation_evidence h)

theorem ay_mwar_validation_requires_defaults
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMWARRehydratedSatValidation
      (AyMWARRehydrationEvidence
        membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    defaultsOk :=
  fun h =>
    ay_mwar_rehydration_evidence_defaults
      (ay_mwar_rehydrated_sat_validation_evidence h)

theorem ay_mwar_validation_requires_projection
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMWARRehydratedSatValidation
      (AyMWARRehydrationEvidence
        membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    projectionOk :=
  fun h =>
    ay_mwar_rehydration_evidence_projection
      (ay_mwar_rehydrated_sat_validation_evidence h)

theorem ay_mwar_validation_requires_checker
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMWARRehydratedSatValidation
      (AyMWARRehydrationEvidence
        membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    checkerOk :=
  fun h =>
    ay_mwar_rehydration_evidence_checker
      (ay_mwar_rehydrated_sat_validation_evidence h)

theorem ay_mwar_validation_requires_fingerprint
    {membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
      fingerprintOk auditEntry publicSatModel : Prop} :
    AyMWARRehydratedSatValidation
      (AyMWARRehydrationEvidence
        membershipOk digestOk mapOk defaultsOk projectionOk checkerOk
        fingerprintOk)
      auditEntry
      publicSatModel ->
    fingerprintOk :=
  fun h =>
    ay_mwar_rehydration_evidence_fingerprint
      (ay_mwar_rehydrated_sat_validation_evidence h)

theorem ay_mwar_rehydrated_sat_validation_sound_exact
    {rehydrationEvidence auditEntry publicSatModel : Prop} :
    AyMWAREquisat
      (AyMWARRehydratedSatValidation
        rehydrationEvidence auditEntry publicSatModel)
      (AyMWARConj rehydrationEvidence
        (AyMWARConj auditEntry publicSatModel)) :=
  ay_mwar_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_mwar_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMWARNoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_mwar_conj_intro hdiagnostic hblocks

theorem ay_mwar_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMWARNoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_mwar_conj_left h

theorem ay_mwar_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMWARNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_mwar_conj_right h

theorem ay_mwar_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMWARRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_mwar_conj_intro hreason hrequest

theorem ay_mwar_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMWARRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_mwar_conj_left h

theorem ay_mwar_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMWARRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_mwar_conj_right h

theorem ay_mwar_missing_archive_entry_recompute
    {missingArchiveEntry recomputeRequest : Prop} :
    missingArchiveEntry ->
    recomputeRequest ->
    AyMWARRecomputeObligation missingArchiveEntry recomputeRequest :=
  fun hmissing hrecompute =>
    ay_mwar_recompute_obligation_intro hmissing hrecompute

theorem ay_mwar_missing_archive_entry_no_claim
    {missingArchiveEntry publicClaim : Prop} :
    missingArchiveEntry ->
    (missingArchiveEntry -> publicClaim -> False) ->
    AyMWARNoClaimDiagnostic missingArchiveEntry publicClaim :=
  fun hmissing hblocks =>
    ay_mwar_no_claim_diagnostic_intro hmissing (hblocks hmissing)

theorem ay_mwar_stale_witness_digest_no_claim
    {staleWitnessDigest publicClaim : Prop} :
    staleWitnessDigest ->
    (staleWitnessDigest -> publicClaim -> False) ->
    AyMWARNoClaimDiagnostic staleWitnessDigest publicClaim :=
  fun hstale hblocks =>
    ay_mwar_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_mwar_variable_map_mismatch_no_claim
    {variableMapMismatch publicClaim : Prop} :
    variableMapMismatch ->
    (variableMapMismatch -> publicClaim -> False) ->
    AyMWARNoClaimDiagnostic variableMapMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mwar_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mwar_missing_defaults_no_claim
    {missingDefaults publicClaim : Prop} :
    missingDefaults ->
    (missingDefaults -> publicClaim -> False) ->
    AyMWARNoClaimDiagnostic missingDefaults publicClaim :=
  fun hmissing hblocks =>
    ay_mwar_no_claim_diagnostic_intro hmissing (hblocks hmissing)

theorem ay_mwar_checker_rejection_no_claim
    {checkerRejection publicClaim : Prop} :
    checkerRejection ->
    (checkerRejection -> publicClaim -> False) ->
    AyMWARNoClaimDiagnostic checkerRejection publicClaim :=
  fun hreject hblocks =>
    ay_mwar_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_mwar_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicClaim : Prop} :
    fingerprintMismatch ->
    (fingerprintMismatch -> publicClaim -> False) ->
    AyMWARNoClaimDiagnostic fingerprintMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mwar_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mwar_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMWARNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_mwar_no_claim_diagnostic_blocks h hclaim

theorem ay_mwar_bad_rehydration_no_stale_sat_validation
    {missingArchiveEntry staleWitnessDigest variableMapMismatch
      missingDefaults checkerRejection fingerprintMismatch publicClaim :
      Prop} :
    (missingArchiveEntry -> publicClaim -> False) ->
    (staleWitnessDigest -> publicClaim -> False) ->
    (variableMapMismatch -> publicClaim -> False) ->
    (missingDefaults -> publicClaim -> False) ->
    (checkerRejection -> publicClaim -> False) ->
    (fingerprintMismatch -> publicClaim -> False) ->
    AyMWARConj
      (missingArchiveEntry ->
        AyMWARNoClaimDiagnostic missingArchiveEntry publicClaim)
      (AyMWARConj
        (staleWitnessDigest ->
          AyMWARNoClaimDiagnostic staleWitnessDigest publicClaim)
        (AyMWARConj
          (variableMapMismatch ->
            AyMWARNoClaimDiagnostic variableMapMismatch publicClaim)
          (AyMWARConj
            (missingDefaults ->
              AyMWARNoClaimDiagnostic missingDefaults publicClaim)
            (AyMWARConj
              (checkerRejection ->
                AyMWARNoClaimDiagnostic checkerRejection publicClaim)
              (fingerprintMismatch ->
                AyMWARNoClaimDiagnostic
                  fingerprintMismatch publicClaim))))) :=
  fun hmissing hdigest hmap hdefaults hchecker hfingerprint =>
    ay_mwar_conj_intro
      (fun h => ay_mwar_missing_archive_entry_no_claim h hmissing)
      (ay_mwar_conj_intro
        (fun h => ay_mwar_stale_witness_digest_no_claim h hdigest)
        (ay_mwar_conj_intro
          (fun h => ay_mwar_variable_map_mismatch_no_claim h hmap)
          (ay_mwar_conj_intro
            (fun h => ay_mwar_missing_defaults_no_claim h hdefaults)
            (ay_mwar_conj_intro
              (fun h => ay_mwar_checker_rejection_no_claim h hchecker)
              (fun h =>
                ay_mwar_fingerprint_mismatch_no_claim h hfingerprint)))))
