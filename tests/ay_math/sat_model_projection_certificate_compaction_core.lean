-- SAT-COMP/ay model projection certificate compaction soundness skeleton.
-- Projection/reconstruction certificates may be compacted for SAT model output
-- only when compact membership, maps, defaults, projection witnesses, replay,
-- digest, and exit-code evidence all agree.

def AyMPCCConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMPCCDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMPCCEquisat (left right : Prop) : Prop :=
  AyMPCCConj (left -> right) (right -> left)

def AyMPCCCompactedMembership
    (fullCertificate compactCertificate requiredDataPresent : Prop) : Prop :=
  AyMPCCConj fullCertificate
    (AyMPCCConj compactCertificate requiredDataPresent)

def AyMPCCVariableMap
    (internalVariableMap originalVariableMap mapAgreement : Prop) : Prop :=
  AyMPCCConj internalVariableMap
    (AyMPCCConj originalVariableMap mapAgreement)

def AyMPCCEliminatedDefaults
    (eliminatedVariables defaultAssignments defaultsComplete : Prop) : Prop :=
  AyMPCCConj eliminatedVariables
    (AyMPCCConj defaultAssignments defaultsComplete)

def AyMPCCProjectionWitness
    (projectionData reconstructionData witnessComplete : Prop) : Prop :=
  AyMPCCConj projectionData
    (AyMPCCConj reconstructionData witnessComplete)

def AyMPCCModelCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMPCCConj checkerAccepted replayTrace

def AyMPCCManifestDigest
    (manifestEntry compactDigest digestAgreement : Prop) : Prop :=
  AyMPCCConj manifestEntry (AyMPCCConj compactDigest digestAgreement)

def AyMPCCExitCodeContract
    (satExitCode outputContract noErrorExit : Prop) : Prop :=
  AyMPCCConj satExitCode (AyMPCCConj outputContract noErrorExit)

def AyMPCCCompactionEvidence
    (membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk :
      Prop) : Prop :=
  AyMPCCConj membershipOk
    (AyMPCCConj mapOk
      (AyMPCCConj defaultsOk
        (AyMPCCConj projectionOk
          (AyMPCCConj checkerOk
            (AyMPCCConj digestOk exitOk)))))

def AyMPCCSatEmission
    (compactionEvidence auditEntry publicSatOutput : Prop) : Prop :=
  AyMPCCConj compactionEvidence
    (AyMPCCConj auditEntry publicSatOutput)

def AyMPCCNoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMPCCConj diagnostic (publicClaim -> False)

def AyMPCCRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMPCCConj reason recomputeRequest

theorem ay_mpcc_conj_intro {left right : Prop} :
    left -> right -> AyMPCCConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mpcc_conj_left {left right : Prop} :
    AyMPCCConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mpcc_conj_right {left right : Prop} :
    AyMPCCConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mpcc_disj_left {left right : Prop} :
    left -> AyMPCCDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mpcc_disj_right {left right : Prop} :
    right -> AyMPCCDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mpcc_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMPCCEquisat left right :=
  fun hf hb => ay_mpcc_conj_intro hf hb

theorem ay_mpcc_equisat_forward {left right : Prop} :
    AyMPCCEquisat left right -> left -> right :=
  fun h => ay_mpcc_conj_left h

theorem ay_mpcc_equisat_backward {left right : Prop} :
    AyMPCCEquisat left right -> right -> left :=
  fun h => ay_mpcc_conj_right h

theorem ay_mpcc_compacted_membership_intro
    {fullCertificate compactCertificate requiredDataPresent : Prop} :
    fullCertificate ->
    compactCertificate ->
    requiredDataPresent ->
    AyMPCCCompactedMembership
      fullCertificate compactCertificate requiredDataPresent :=
  fun hfull hcompact hrequired =>
    ay_mpcc_conj_intro hfull
      (ay_mpcc_conj_intro hcompact hrequired)

theorem ay_mpcc_compacted_membership_full
    {fullCertificate compactCertificate requiredDataPresent : Prop} :
    AyMPCCCompactedMembership
      fullCertificate compactCertificate requiredDataPresent ->
    fullCertificate :=
  fun h => ay_mpcc_conj_left h

theorem ay_mpcc_compacted_membership_compact
    {fullCertificate compactCertificate requiredDataPresent : Prop} :
    AyMPCCCompactedMembership
      fullCertificate compactCertificate requiredDataPresent ->
    compactCertificate :=
  fun h => ay_mpcc_conj_left (ay_mpcc_conj_right h)

theorem ay_mpcc_compacted_membership_required
    {fullCertificate compactCertificate requiredDataPresent : Prop} :
    AyMPCCCompactedMembership
      fullCertificate compactCertificate requiredDataPresent ->
    requiredDataPresent :=
  fun h => ay_mpcc_conj_right (ay_mpcc_conj_right h)

theorem ay_mpcc_variable_map_intro
    {internalVariableMap originalVariableMap mapAgreement : Prop} :
    internalVariableMap ->
    originalVariableMap ->
    mapAgreement ->
    AyMPCCVariableMap internalVariableMap originalVariableMap mapAgreement :=
  fun hinternal horiginal hagree =>
    ay_mpcc_conj_intro hinternal
      (ay_mpcc_conj_intro horiginal hagree)

theorem ay_mpcc_variable_map_internal
    {internalVariableMap originalVariableMap mapAgreement : Prop} :
    AyMPCCVariableMap internalVariableMap originalVariableMap mapAgreement ->
    internalVariableMap :=
  fun h => ay_mpcc_conj_left h

theorem ay_mpcc_variable_map_original
    {internalVariableMap originalVariableMap mapAgreement : Prop} :
    AyMPCCVariableMap internalVariableMap originalVariableMap mapAgreement ->
    originalVariableMap :=
  fun h => ay_mpcc_conj_left (ay_mpcc_conj_right h)

theorem ay_mpcc_variable_map_agreement
    {internalVariableMap originalVariableMap mapAgreement : Prop} :
    AyMPCCVariableMap internalVariableMap originalVariableMap mapAgreement ->
    mapAgreement :=
  fun h => ay_mpcc_conj_right (ay_mpcc_conj_right h)

theorem ay_mpcc_eliminated_defaults_intro
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    eliminatedVariables ->
    defaultAssignments ->
    defaultsComplete ->
    AyMPCCEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete :=
  fun helim hdefaults hcomplete =>
    ay_mpcc_conj_intro helim
      (ay_mpcc_conj_intro hdefaults hcomplete)

theorem ay_mpcc_eliminated_defaults_variables
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMPCCEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    eliminatedVariables :=
  fun h => ay_mpcc_conj_left h

theorem ay_mpcc_eliminated_defaults_assignments
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMPCCEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    defaultAssignments :=
  fun h => ay_mpcc_conj_left (ay_mpcc_conj_right h)

theorem ay_mpcc_eliminated_defaults_complete
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMPCCEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    defaultsComplete :=
  fun h => ay_mpcc_conj_right (ay_mpcc_conj_right h)

theorem ay_mpcc_projection_witness_intro
    {projectionData reconstructionData witnessComplete : Prop} :
    projectionData ->
    reconstructionData ->
    witnessComplete ->
    AyMPCCProjectionWitness
      projectionData reconstructionData witnessComplete :=
  fun hprojection hreconstruction hcomplete =>
    ay_mpcc_conj_intro hprojection
      (ay_mpcc_conj_intro hreconstruction hcomplete)

theorem ay_mpcc_projection_witness_projection
    {projectionData reconstructionData witnessComplete : Prop} :
    AyMPCCProjectionWitness
      projectionData reconstructionData witnessComplete ->
    projectionData :=
  fun h => ay_mpcc_conj_left h

theorem ay_mpcc_projection_witness_reconstruction
    {projectionData reconstructionData witnessComplete : Prop} :
    AyMPCCProjectionWitness
      projectionData reconstructionData witnessComplete ->
    reconstructionData :=
  fun h => ay_mpcc_conj_left (ay_mpcc_conj_right h)

theorem ay_mpcc_projection_witness_complete
    {projectionData reconstructionData witnessComplete : Prop} :
    AyMPCCProjectionWitness
      projectionData reconstructionData witnessComplete ->
    witnessComplete :=
  fun h => ay_mpcc_conj_right (ay_mpcc_conj_right h)

theorem ay_mpcc_model_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMPCCModelCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mpcc_conj_intro haccepted htrace

theorem ay_mpcc_model_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMPCCModelCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_mpcc_conj_left h

theorem ay_mpcc_model_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMPCCModelCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_mpcc_conj_right h

theorem ay_mpcc_manifest_digest_intro
    {manifestEntry compactDigest digestAgreement : Prop} :
    manifestEntry ->
    compactDigest ->
    digestAgreement ->
    AyMPCCManifestDigest manifestEntry compactDigest digestAgreement :=
  fun hmanifest hdigest hagree =>
    ay_mpcc_conj_intro hmanifest
      (ay_mpcc_conj_intro hdigest hagree)

theorem ay_mpcc_manifest_digest_entry
    {manifestEntry compactDigest digestAgreement : Prop} :
    AyMPCCManifestDigest manifestEntry compactDigest digestAgreement ->
    manifestEntry :=
  fun h => ay_mpcc_conj_left h

theorem ay_mpcc_manifest_digest_compact
    {manifestEntry compactDigest digestAgreement : Prop} :
    AyMPCCManifestDigest manifestEntry compactDigest digestAgreement ->
    compactDigest :=
  fun h => ay_mpcc_conj_left (ay_mpcc_conj_right h)

theorem ay_mpcc_manifest_digest_agreement
    {manifestEntry compactDigest digestAgreement : Prop} :
    AyMPCCManifestDigest manifestEntry compactDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mpcc_conj_right (ay_mpcc_conj_right h)

theorem ay_mpcc_exit_code_contract_intro
    {satExitCode outputContract noErrorExit : Prop} :
    satExitCode ->
    outputContract ->
    noErrorExit ->
    AyMPCCExitCodeContract satExitCode outputContract noErrorExit :=
  fun hexit houtput hnoerror =>
    ay_mpcc_conj_intro hexit (ay_mpcc_conj_intro houtput hnoerror)

theorem ay_mpcc_exit_code_contract_sat
    {satExitCode outputContract noErrorExit : Prop} :
    AyMPCCExitCodeContract satExitCode outputContract noErrorExit ->
    satExitCode :=
  fun h => ay_mpcc_conj_left h

theorem ay_mpcc_exit_code_contract_output
    {satExitCode outputContract noErrorExit : Prop} :
    AyMPCCExitCodeContract satExitCode outputContract noErrorExit ->
    outputContract :=
  fun h => ay_mpcc_conj_left (ay_mpcc_conj_right h)

theorem ay_mpcc_exit_code_contract_no_error
    {satExitCode outputContract noErrorExit : Prop} :
    AyMPCCExitCodeContract satExitCode outputContract noErrorExit ->
    noErrorExit :=
  fun h => ay_mpcc_conj_right (ay_mpcc_conj_right h)

theorem ay_mpcc_compaction_evidence_intro
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk :
      Prop} :
    membershipOk ->
    mapOk ->
    defaultsOk ->
    projectionOk ->
    checkerOk ->
    digestOk ->
    exitOk ->
    AyMPCCCompactionEvidence
      membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk :=
  fun hmembership hmap hdefaults hprojection hchecker hdigest hexit =>
    ay_mpcc_conj_intro hmembership
      (ay_mpcc_conj_intro hmap
        (ay_mpcc_conj_intro hdefaults
          (ay_mpcc_conj_intro hprojection
            (ay_mpcc_conj_intro hchecker
              (ay_mpcc_conj_intro hdigest hexit)))))

theorem ay_mpcc_compaction_evidence_membership
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk :
      Prop} :
    AyMPCCCompactionEvidence
      membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk ->
    membershipOk :=
  fun h => ay_mpcc_conj_left h

theorem ay_mpcc_compaction_evidence_map
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk :
      Prop} :
    AyMPCCCompactionEvidence
      membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk ->
    mapOk :=
  fun h => ay_mpcc_conj_left (ay_mpcc_conj_right h)

theorem ay_mpcc_compaction_evidence_defaults
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk :
      Prop} :
    AyMPCCCompactionEvidence
      membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk ->
    defaultsOk :=
  fun h => ay_mpcc_conj_left (ay_mpcc_conj_right (ay_mpcc_conj_right h))

theorem ay_mpcc_compaction_evidence_projection
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk :
      Prop} :
    AyMPCCCompactionEvidence
      membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk ->
    projectionOk :=
  fun h =>
    ay_mpcc_conj_left
      (ay_mpcc_conj_right (ay_mpcc_conj_right (ay_mpcc_conj_right h)))

theorem ay_mpcc_compaction_evidence_checker
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk :
      Prop} :
    AyMPCCCompactionEvidence
      membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk ->
    checkerOk :=
  fun h =>
    ay_mpcc_conj_left
      (ay_mpcc_conj_right
        (ay_mpcc_conj_right (ay_mpcc_conj_right (ay_mpcc_conj_right h))))

theorem ay_mpcc_compaction_evidence_digest
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk :
      Prop} :
    AyMPCCCompactionEvidence
      membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk ->
    digestOk :=
  fun h =>
    ay_mpcc_conj_left
      (ay_mpcc_conj_right
        (ay_mpcc_conj_right
          (ay_mpcc_conj_right (ay_mpcc_conj_right (ay_mpcc_conj_right h)))))

theorem ay_mpcc_compaction_evidence_exit
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk :
      Prop} :
    AyMPCCCompactionEvidence
      membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk ->
    exitOk :=
  fun h =>
    ay_mpcc_conj_right
      (ay_mpcc_conj_right
        (ay_mpcc_conj_right
          (ay_mpcc_conj_right (ay_mpcc_conj_right (ay_mpcc_conj_right h)))))

theorem ay_mpcc_sat_emission_intro
    {compactionEvidence auditEntry publicSatOutput : Prop} :
    compactionEvidence ->
    auditEntry ->
    publicSatOutput ->
    AyMPCCSatEmission compactionEvidence auditEntry publicSatOutput :=
  fun hevidence haudit houtput =>
    ay_mpcc_conj_intro hevidence (ay_mpcc_conj_intro haudit houtput)

theorem ay_mpcc_sat_emission_evidence
    {compactionEvidence auditEntry publicSatOutput : Prop} :
    AyMPCCSatEmission compactionEvidence auditEntry publicSatOutput ->
    compactionEvidence :=
  fun h => ay_mpcc_conj_left h

theorem ay_mpcc_sat_emission_audit
    {compactionEvidence auditEntry publicSatOutput : Prop} :
    AyMPCCSatEmission compactionEvidence auditEntry publicSatOutput ->
    auditEntry :=
  fun h => ay_mpcc_conj_left (ay_mpcc_conj_right h)

theorem ay_mpcc_sat_emission_output
    {compactionEvidence auditEntry publicSatOutput : Prop} :
    AyMPCCSatEmission compactionEvidence auditEntry publicSatOutput ->
    publicSatOutput :=
  fun h => ay_mpcc_conj_right (ay_mpcc_conj_right h)

theorem ay_mpcc_accepted_compaction_preserves_sat_publication
    {compactionEvidence auditEntry publicSatOutput : Prop} :
    AyMPCCSatEmission compactionEvidence auditEntry publicSatOutput ->
    publicSatOutput :=
  fun h => ay_mpcc_sat_emission_output h

theorem ay_mpcc_publication_requires_membership
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMPCCSatEmission
      (AyMPCCCompactionEvidence
        membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    membershipOk :=
  fun h =>
    ay_mpcc_compaction_evidence_membership
      (ay_mpcc_sat_emission_evidence h)

theorem ay_mpcc_publication_requires_map
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMPCCSatEmission
      (AyMPCCCompactionEvidence
        membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    mapOk :=
  fun h =>
    ay_mpcc_compaction_evidence_map
      (ay_mpcc_sat_emission_evidence h)

theorem ay_mpcc_publication_requires_defaults
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMPCCSatEmission
      (AyMPCCCompactionEvidence
        membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    defaultsOk :=
  fun h =>
    ay_mpcc_compaction_evidence_defaults
      (ay_mpcc_sat_emission_evidence h)

theorem ay_mpcc_publication_requires_projection
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMPCCSatEmission
      (AyMPCCCompactionEvidence
        membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    projectionOk :=
  fun h =>
    ay_mpcc_compaction_evidence_projection
      (ay_mpcc_sat_emission_evidence h)

theorem ay_mpcc_publication_requires_checker
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMPCCSatEmission
      (AyMPCCCompactionEvidence
        membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    checkerOk :=
  fun h =>
    ay_mpcc_compaction_evidence_checker
      (ay_mpcc_sat_emission_evidence h)

theorem ay_mpcc_publication_requires_digest
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMPCCSatEmission
      (AyMPCCCompactionEvidence
        membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    digestOk :=
  fun h =>
    ay_mpcc_compaction_evidence_digest
      (ay_mpcc_sat_emission_evidence h)

theorem ay_mpcc_publication_requires_exit_contract
    {membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMPCCSatEmission
      (AyMPCCCompactionEvidence
        membershipOk mapOk defaultsOk projectionOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    exitOk :=
  fun h =>
    ay_mpcc_compaction_evidence_exit
      (ay_mpcc_sat_emission_evidence h)

theorem ay_mpcc_sat_emission_sound_exact
    {compactionEvidence auditEntry publicSatOutput : Prop} :
    AyMPCCEquisat
      (AyMPCCSatEmission compactionEvidence auditEntry publicSatOutput)
      (AyMPCCConj compactionEvidence
        (AyMPCCConj auditEntry publicSatOutput)) :=
  ay_mpcc_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_mpcc_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMPCCNoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_mpcc_conj_intro hdiagnostic hblocks

theorem ay_mpcc_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMPCCNoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_mpcc_conj_left h

theorem ay_mpcc_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMPCCNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_mpcc_conj_right h

theorem ay_mpcc_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMPCCRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_mpcc_conj_intro hreason hrequest

theorem ay_mpcc_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMPCCRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_mpcc_conj_left h

theorem ay_mpcc_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMPCCRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_mpcc_conj_right h

theorem ay_mpcc_omitted_projection_data_recompute
    {omittedProjectionData recomputeRequest : Prop} :
    omittedProjectionData ->
    recomputeRequest ->
    AyMPCCRecomputeObligation omittedProjectionData recomputeRequest :=
  fun homitted hrecompute =>
    ay_mpcc_recompute_obligation_intro homitted hrecompute

theorem ay_mpcc_omitted_projection_data_no_claim
    {omittedProjectionData publicClaim : Prop} :
    omittedProjectionData ->
    (omittedProjectionData -> publicClaim -> False) ->
    AyMPCCNoClaimDiagnostic omittedProjectionData publicClaim :=
  fun homitted hblocks =>
    ay_mpcc_no_claim_diagnostic_intro homitted (hblocks homitted)

theorem ay_mpcc_stale_compact_certificate_no_claim
    {staleCompactCertificate publicClaim : Prop} :
    staleCompactCertificate ->
    (staleCompactCertificate -> publicClaim -> False) ->
    AyMPCCNoClaimDiagnostic staleCompactCertificate publicClaim :=
  fun hstale hblocks =>
    ay_mpcc_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_mpcc_variable_map_mismatch_no_claim
    {variableMapMismatch publicClaim : Prop} :
    variableMapMismatch ->
    (variableMapMismatch -> publicClaim -> False) ->
    AyMPCCNoClaimDiagnostic variableMapMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mpcc_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mpcc_digest_mismatch_no_claim
    {digestMismatch publicClaim : Prop} :
    digestMismatch ->
    (digestMismatch -> publicClaim -> False) ->
    AyMPCCNoClaimDiagnostic digestMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mpcc_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mpcc_checker_rejection_no_claim
    {checkerRejection publicClaim : Prop} :
    checkerRejection ->
    (checkerRejection -> publicClaim -> False) ->
    AyMPCCNoClaimDiagnostic checkerRejection publicClaim :=
  fun hreject hblocks =>
    ay_mpcc_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_mpcc_exit_contract_mismatch_no_claim
    {exitContractMismatch publicClaim : Prop} :
    exitContractMismatch ->
    (exitContractMismatch -> publicClaim -> False) ->
    AyMPCCNoClaimDiagnostic exitContractMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mpcc_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mpcc_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMPCCNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_mpcc_no_claim_diagnostic_blocks h hclaim

theorem ay_mpcc_bad_compaction_no_stale_sat_emission
    {omittedProjectionData staleCompactCertificate variableMapMismatch
      digestMismatch checkerRejection exitContractMismatch publicClaim : Prop} :
    (omittedProjectionData -> publicClaim -> False) ->
    (staleCompactCertificate -> publicClaim -> False) ->
    (variableMapMismatch -> publicClaim -> False) ->
    (digestMismatch -> publicClaim -> False) ->
    (checkerRejection -> publicClaim -> False) ->
    (exitContractMismatch -> publicClaim -> False) ->
    AyMPCCConj
      (omittedProjectionData ->
        AyMPCCNoClaimDiagnostic omittedProjectionData publicClaim)
      (AyMPCCConj
        (staleCompactCertificate ->
          AyMPCCNoClaimDiagnostic staleCompactCertificate publicClaim)
        (AyMPCCConj
          (variableMapMismatch ->
            AyMPCCNoClaimDiagnostic variableMapMismatch publicClaim)
          (AyMPCCConj
            (digestMismatch ->
              AyMPCCNoClaimDiagnostic digestMismatch publicClaim)
            (AyMPCCConj
              (checkerRejection ->
                AyMPCCNoClaimDiagnostic checkerRejection publicClaim)
              (exitContractMismatch ->
                AyMPCCNoClaimDiagnostic
                  exitContractMismatch publicClaim))))) :=
  fun homitted hstale hmap hdigest hchecker hexit =>
    ay_mpcc_conj_intro
      (fun h => ay_mpcc_omitted_projection_data_no_claim h homitted)
      (ay_mpcc_conj_intro
        (fun h => ay_mpcc_stale_compact_certificate_no_claim h hstale)
        (ay_mpcc_conj_intro
          (fun h => ay_mpcc_variable_map_mismatch_no_claim h hmap)
          (ay_mpcc_conj_intro
            (fun h => ay_mpcc_digest_mismatch_no_claim h hdigest)
            (ay_mpcc_conj_intro
              (fun h => ay_mpcc_checker_rejection_no_claim h hchecker)
              (fun h => ay_mpcc_exit_contract_mismatch_no_claim h hexit)))))
