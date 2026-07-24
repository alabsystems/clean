-- SAT-COMP/ay SAT model output replay archive soundness skeleton.
-- Archived model output validates a public SAT emission only when archive
-- membership, digest, maps, defaults, replay, exit-code, and original formula
-- fingerprint evidence all agree.

def AyMORAConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMORADisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMORAEquisat (left right : Prop) : Prop :=
  AyMORAConj (left -> right) (right -> left)

def AyMORAArchiveMembership
    (archiveRoot archiveEntry entryIncluded : Prop) : Prop :=
  AyMORAConj archiveRoot (AyMORAConj archiveEntry entryIncluded)

def AyMORAOutputDigest
    (emittedOutput archivedDigest digestAgreement : Prop) : Prop :=
  AyMORAConj emittedOutput (AyMORAConj archivedDigest digestAgreement)

def AyMORAVariableMap
    (outputVariableMap originalVariableMap mapAgreement : Prop) : Prop :=
  AyMORAConj outputVariableMap
    (AyMORAConj originalVariableMap mapAgreement)

def AyMORAEliminatedDefaults
    (eliminatedVariables defaultAssignments defaultsComplete : Prop) : Prop :=
  AyMORAConj eliminatedVariables
    (AyMORAConj defaultAssignments defaultsComplete)

def AyMORAModelCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMORAConj checkerAccepted replayTrace

def AyMORAExitCodeContract
    (satExitCode stdoutContract noErrorExit : Prop) : Prop :=
  AyMORAConj satExitCode (AyMORAConj stdoutContract noErrorExit)

def AyMORAOriginalFormulaFingerprint
    (formulaFingerprint archivedFingerprint fingerprintAgreement : Prop) :
    Prop :=
  AyMORAConj formulaFingerprint
    (AyMORAConj archivedFingerprint fingerprintAgreement)

def AyMORAArchiveValidationEvidence
    (membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk :
      Prop) : Prop :=
  AyMORAConj membershipOk
    (AyMORAConj digestOk
      (AyMORAConj mapOk
        (AyMORAConj defaultsOk
          (AyMORAConj checkerOk
            (AyMORAConj exitOk fingerprintOk)))))

def AyMORAArchivedSatValidation
    (validationEvidence auditEntry publicSatOutput : Prop) : Prop :=
  AyMORAConj validationEvidence
    (AyMORAConj auditEntry publicSatOutput)

def AyMORANoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMORAConj diagnostic (publicClaim -> False)

def AyMORARecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMORAConj reason recomputeRequest

theorem ay_mora_conj_intro {left right : Prop} :
    left -> right -> AyMORAConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_mora_conj_left {left right : Prop} :
    AyMORAConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_mora_conj_right {left right : Prop} :
    AyMORAConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_mora_disj_left {left right : Prop} :
    left -> AyMORADisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_mora_disj_right {left right : Prop} :
    right -> AyMORADisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_mora_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMORAEquisat left right :=
  fun hf hb => ay_mora_conj_intro hf hb

theorem ay_mora_equisat_forward {left right : Prop} :
    AyMORAEquisat left right -> left -> right :=
  fun h => ay_mora_conj_left h

theorem ay_mora_equisat_backward {left right : Prop} :
    AyMORAEquisat left right -> right -> left :=
  fun h => ay_mora_conj_right h

theorem ay_mora_archive_membership_intro
    {archiveRoot archiveEntry entryIncluded : Prop} :
    archiveRoot ->
    archiveEntry ->
    entryIncluded ->
    AyMORAArchiveMembership archiveRoot archiveEntry entryIncluded :=
  fun hroot hentry hincluded =>
    ay_mora_conj_intro hroot (ay_mora_conj_intro hentry hincluded)

theorem ay_mora_archive_membership_root
    {archiveRoot archiveEntry entryIncluded : Prop} :
    AyMORAArchiveMembership archiveRoot archiveEntry entryIncluded ->
    archiveRoot :=
  fun h => ay_mora_conj_left h

theorem ay_mora_archive_membership_entry
    {archiveRoot archiveEntry entryIncluded : Prop} :
    AyMORAArchiveMembership archiveRoot archiveEntry entryIncluded ->
    archiveEntry :=
  fun h => ay_mora_conj_left (ay_mora_conj_right h)

theorem ay_mora_archive_membership_included
    {archiveRoot archiveEntry entryIncluded : Prop} :
    AyMORAArchiveMembership archiveRoot archiveEntry entryIncluded ->
    entryIncluded :=
  fun h => ay_mora_conj_right (ay_mora_conj_right h)

theorem ay_mora_output_digest_intro
    {emittedOutput archivedDigest digestAgreement : Prop} :
    emittedOutput ->
    archivedDigest ->
    digestAgreement ->
    AyMORAOutputDigest emittedOutput archivedDigest digestAgreement :=
  fun hemitted harchived hagree =>
    ay_mora_conj_intro hemitted (ay_mora_conj_intro harchived hagree)

theorem ay_mora_output_digest_emitted
    {emittedOutput archivedDigest digestAgreement : Prop} :
    AyMORAOutputDigest emittedOutput archivedDigest digestAgreement ->
    emittedOutput :=
  fun h => ay_mora_conj_left h

theorem ay_mora_output_digest_archived
    {emittedOutput archivedDigest digestAgreement : Prop} :
    AyMORAOutputDigest emittedOutput archivedDigest digestAgreement ->
    archivedDigest :=
  fun h => ay_mora_conj_left (ay_mora_conj_right h)

theorem ay_mora_output_digest_agreement
    {emittedOutput archivedDigest digestAgreement : Prop} :
    AyMORAOutputDigest emittedOutput archivedDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_mora_conj_right (ay_mora_conj_right h)

theorem ay_mora_variable_map_intro
    {outputVariableMap originalVariableMap mapAgreement : Prop} :
    outputVariableMap ->
    originalVariableMap ->
    mapAgreement ->
    AyMORAVariableMap outputVariableMap originalVariableMap mapAgreement :=
  fun houtput horiginal hagree =>
    ay_mora_conj_intro houtput (ay_mora_conj_intro horiginal hagree)

theorem ay_mora_variable_map_output
    {outputVariableMap originalVariableMap mapAgreement : Prop} :
    AyMORAVariableMap outputVariableMap originalVariableMap mapAgreement ->
    outputVariableMap :=
  fun h => ay_mora_conj_left h

theorem ay_mora_variable_map_original
    {outputVariableMap originalVariableMap mapAgreement : Prop} :
    AyMORAVariableMap outputVariableMap originalVariableMap mapAgreement ->
    originalVariableMap :=
  fun h => ay_mora_conj_left (ay_mora_conj_right h)

theorem ay_mora_variable_map_agreement
    {outputVariableMap originalVariableMap mapAgreement : Prop} :
    AyMORAVariableMap outputVariableMap originalVariableMap mapAgreement ->
    mapAgreement :=
  fun h => ay_mora_conj_right (ay_mora_conj_right h)

theorem ay_mora_eliminated_defaults_intro
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    eliminatedVariables ->
    defaultAssignments ->
    defaultsComplete ->
    AyMORAEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete :=
  fun helim hdefaults hcomplete =>
    ay_mora_conj_intro helim
      (ay_mora_conj_intro hdefaults hcomplete)

theorem ay_mora_eliminated_defaults_variables
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMORAEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    eliminatedVariables :=
  fun h => ay_mora_conj_left h

theorem ay_mora_eliminated_defaults_assignments
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMORAEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    defaultAssignments :=
  fun h => ay_mora_conj_left (ay_mora_conj_right h)

theorem ay_mora_eliminated_defaults_complete
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMORAEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    defaultsComplete :=
  fun h => ay_mora_conj_right (ay_mora_conj_right h)

theorem ay_mora_model_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMORAModelCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_mora_conj_intro haccepted htrace

theorem ay_mora_model_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMORAModelCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_mora_conj_left h

theorem ay_mora_model_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMORAModelCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_mora_conj_right h

theorem ay_mora_exit_code_contract_intro
    {satExitCode stdoutContract noErrorExit : Prop} :
    satExitCode ->
    stdoutContract ->
    noErrorExit ->
    AyMORAExitCodeContract satExitCode stdoutContract noErrorExit :=
  fun hexit hstdout hnoerror =>
    ay_mora_conj_intro hexit (ay_mora_conj_intro hstdout hnoerror)

theorem ay_mora_exit_code_contract_sat
    {satExitCode stdoutContract noErrorExit : Prop} :
    AyMORAExitCodeContract satExitCode stdoutContract noErrorExit ->
    satExitCode :=
  fun h => ay_mora_conj_left h

theorem ay_mora_exit_code_contract_stdout
    {satExitCode stdoutContract noErrorExit : Prop} :
    AyMORAExitCodeContract satExitCode stdoutContract noErrorExit ->
    stdoutContract :=
  fun h => ay_mora_conj_left (ay_mora_conj_right h)

theorem ay_mora_exit_code_contract_no_error
    {satExitCode stdoutContract noErrorExit : Prop} :
    AyMORAExitCodeContract satExitCode stdoutContract noErrorExit ->
    noErrorExit :=
  fun h => ay_mora_conj_right (ay_mora_conj_right h)

theorem ay_mora_original_formula_fingerprint_intro
    {formulaFingerprint archivedFingerprint fingerprintAgreement : Prop} :
    formulaFingerprint ->
    archivedFingerprint ->
    fingerprintAgreement ->
    AyMORAOriginalFormulaFingerprint
      formulaFingerprint archivedFingerprint fingerprintAgreement :=
  fun hformula harchived hagree =>
    ay_mora_conj_intro hformula
      (ay_mora_conj_intro harchived hagree)

theorem ay_mora_original_formula_fingerprint_formula
    {formulaFingerprint archivedFingerprint fingerprintAgreement : Prop} :
    AyMORAOriginalFormulaFingerprint
      formulaFingerprint archivedFingerprint fingerprintAgreement ->
    formulaFingerprint :=
  fun h => ay_mora_conj_left h

theorem ay_mora_original_formula_fingerprint_archived
    {formulaFingerprint archivedFingerprint fingerprintAgreement : Prop} :
    AyMORAOriginalFormulaFingerprint
      formulaFingerprint archivedFingerprint fingerprintAgreement ->
    archivedFingerprint :=
  fun h => ay_mora_conj_left (ay_mora_conj_right h)

theorem ay_mora_original_formula_fingerprint_agreement
    {formulaFingerprint archivedFingerprint fingerprintAgreement : Prop} :
    AyMORAOriginalFormulaFingerprint
      formulaFingerprint archivedFingerprint fingerprintAgreement ->
    fingerprintAgreement :=
  fun h => ay_mora_conj_right (ay_mora_conj_right h)

theorem ay_mora_archive_validation_evidence_intro
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk :
      Prop} :
    membershipOk ->
    digestOk ->
    mapOk ->
    defaultsOk ->
    checkerOk ->
    exitOk ->
    fingerprintOk ->
    AyMORAArchiveValidationEvidence
      membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk :=
  fun hmembership hdigest hmap hdefaults hchecker hexit hfingerprint =>
    ay_mora_conj_intro hmembership
      (ay_mora_conj_intro hdigest
        (ay_mora_conj_intro hmap
          (ay_mora_conj_intro hdefaults
            (ay_mora_conj_intro hchecker
              (ay_mora_conj_intro hexit hfingerprint)))))

theorem ay_mora_archive_validation_evidence_membership
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk :
      Prop} :
    AyMORAArchiveValidationEvidence
      membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk ->
    membershipOk :=
  fun h => ay_mora_conj_left h

theorem ay_mora_archive_validation_evidence_digest
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk :
      Prop} :
    AyMORAArchiveValidationEvidence
      membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk ->
    digestOk :=
  fun h => ay_mora_conj_left (ay_mora_conj_right h)

theorem ay_mora_archive_validation_evidence_map
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk :
      Prop} :
    AyMORAArchiveValidationEvidence
      membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk ->
    mapOk :=
  fun h => ay_mora_conj_left (ay_mora_conj_right (ay_mora_conj_right h))

theorem ay_mora_archive_validation_evidence_defaults
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk :
      Prop} :
    AyMORAArchiveValidationEvidence
      membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk ->
    defaultsOk :=
  fun h =>
    ay_mora_conj_left
      (ay_mora_conj_right (ay_mora_conj_right (ay_mora_conj_right h)))

theorem ay_mora_archive_validation_evidence_checker
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk :
      Prop} :
    AyMORAArchiveValidationEvidence
      membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk ->
    checkerOk :=
  fun h =>
    ay_mora_conj_left
      (ay_mora_conj_right
        (ay_mora_conj_right (ay_mora_conj_right (ay_mora_conj_right h))))

theorem ay_mora_archive_validation_evidence_exit
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk :
      Prop} :
    AyMORAArchiveValidationEvidence
      membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk ->
    exitOk :=
  fun h =>
    ay_mora_conj_left
      (ay_mora_conj_right
        (ay_mora_conj_right
          (ay_mora_conj_right (ay_mora_conj_right (ay_mora_conj_right h)))))

theorem ay_mora_archive_validation_evidence_fingerprint
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk :
      Prop} :
    AyMORAArchiveValidationEvidence
      membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk ->
    fingerprintOk :=
  fun h =>
    ay_mora_conj_right
      (ay_mora_conj_right
        (ay_mora_conj_right
          (ay_mora_conj_right (ay_mora_conj_right (ay_mora_conj_right h)))))

theorem ay_mora_archived_sat_validation_intro
    {validationEvidence auditEntry publicSatOutput : Prop} :
    validationEvidence ->
    auditEntry ->
    publicSatOutput ->
    AyMORAArchivedSatValidation
      validationEvidence auditEntry publicSatOutput :=
  fun hevidence haudit houtput =>
    ay_mora_conj_intro hevidence (ay_mora_conj_intro haudit houtput)

theorem ay_mora_archived_sat_validation_evidence
    {validationEvidence auditEntry publicSatOutput : Prop} :
    AyMORAArchivedSatValidation validationEvidence auditEntry publicSatOutput ->
    validationEvidence :=
  fun h => ay_mora_conj_left h

theorem ay_mora_archived_sat_validation_audit
    {validationEvidence auditEntry publicSatOutput : Prop} :
    AyMORAArchivedSatValidation validationEvidence auditEntry publicSatOutput ->
    auditEntry :=
  fun h => ay_mora_conj_left (ay_mora_conj_right h)

theorem ay_mora_archived_sat_validation_output
    {validationEvidence auditEntry publicSatOutput : Prop} :
    AyMORAArchivedSatValidation validationEvidence auditEntry publicSatOutput ->
    publicSatOutput :=
  fun h => ay_mora_conj_right (ay_mora_conj_right h)

theorem ay_mora_accepted_archive_validates_sat_publication
    {validationEvidence auditEntry publicSatOutput : Prop} :
    AyMORAArchivedSatValidation validationEvidence auditEntry publicSatOutput ->
    publicSatOutput :=
  fun h => ay_mora_archived_sat_validation_output h

theorem ay_mora_validation_requires_membership
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk
      auditEntry publicSatOutput : Prop} :
    AyMORAArchivedSatValidation
      (AyMORAArchiveValidationEvidence
        membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk)
      auditEntry
      publicSatOutput ->
    membershipOk :=
  fun h =>
    ay_mora_archive_validation_evidence_membership
      (ay_mora_archived_sat_validation_evidence h)

theorem ay_mora_validation_requires_digest
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk
      auditEntry publicSatOutput : Prop} :
    AyMORAArchivedSatValidation
      (AyMORAArchiveValidationEvidence
        membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk)
      auditEntry
      publicSatOutput ->
    digestOk :=
  fun h =>
    ay_mora_archive_validation_evidence_digest
      (ay_mora_archived_sat_validation_evidence h)

theorem ay_mora_validation_requires_map
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk
      auditEntry publicSatOutput : Prop} :
    AyMORAArchivedSatValidation
      (AyMORAArchiveValidationEvidence
        membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk)
      auditEntry
      publicSatOutput ->
    mapOk :=
  fun h =>
    ay_mora_archive_validation_evidence_map
      (ay_mora_archived_sat_validation_evidence h)

theorem ay_mora_validation_requires_checker
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk
      auditEntry publicSatOutput : Prop} :
    AyMORAArchivedSatValidation
      (AyMORAArchiveValidationEvidence
        membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk)
      auditEntry
      publicSatOutput ->
    checkerOk :=
  fun h =>
    ay_mora_archive_validation_evidence_checker
      (ay_mora_archived_sat_validation_evidence h)

theorem ay_mora_validation_requires_exit
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk
      auditEntry publicSatOutput : Prop} :
    AyMORAArchivedSatValidation
      (AyMORAArchiveValidationEvidence
        membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk)
      auditEntry
      publicSatOutput ->
    exitOk :=
  fun h =>
    ay_mora_archive_validation_evidence_exit
      (ay_mora_archived_sat_validation_evidence h)

theorem ay_mora_validation_requires_fingerprint
    {membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk
      auditEntry publicSatOutput : Prop} :
    AyMORAArchivedSatValidation
      (AyMORAArchiveValidationEvidence
        membershipOk digestOk mapOk defaultsOk checkerOk exitOk fingerprintOk)
      auditEntry
      publicSatOutput ->
    fingerprintOk :=
  fun h =>
    ay_mora_archive_validation_evidence_fingerprint
      (ay_mora_archived_sat_validation_evidence h)

theorem ay_mora_archived_sat_validation_sound_exact
    {validationEvidence auditEntry publicSatOutput : Prop} :
    AyMORAEquisat
      (AyMORAArchivedSatValidation
        validationEvidence auditEntry publicSatOutput)
      (AyMORAConj validationEvidence
        (AyMORAConj auditEntry publicSatOutput)) :=
  ay_mora_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_mora_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMORANoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_mora_conj_intro hdiagnostic hblocks

theorem ay_mora_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMORANoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_mora_conj_left h

theorem ay_mora_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMORANoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_mora_conj_right h

theorem ay_mora_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMORARecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_mora_conj_intro hreason hrequest

theorem ay_mora_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMORARecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_mora_conj_left h

theorem ay_mora_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMORARecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_mora_conj_right h

theorem ay_mora_missing_archive_entry_recompute
    {missingArchiveEntry recomputeRequest : Prop} :
    missingArchiveEntry ->
    recomputeRequest ->
    AyMORARecomputeObligation missingArchiveEntry recomputeRequest :=
  fun hmissing hrecompute =>
    ay_mora_recompute_obligation_intro hmissing hrecompute

theorem ay_mora_missing_archive_entry_no_claim
    {missingArchiveEntry publicClaim : Prop} :
    missingArchiveEntry ->
    (missingArchiveEntry -> publicClaim -> False) ->
    AyMORANoClaimDiagnostic missingArchiveEntry publicClaim :=
  fun hmissing hblocks =>
    ay_mora_no_claim_diagnostic_intro hmissing (hblocks hmissing)

theorem ay_mora_stale_output_digest_no_claim
    {staleOutputDigest publicClaim : Prop} :
    staleOutputDigest ->
    (staleOutputDigest -> publicClaim -> False) ->
    AyMORANoClaimDiagnostic staleOutputDigest publicClaim :=
  fun hstale hblocks =>
    ay_mora_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_mora_variable_map_mismatch_no_claim
    {variableMapMismatch publicClaim : Prop} :
    variableMapMismatch ->
    (variableMapMismatch -> publicClaim -> False) ->
    AyMORANoClaimDiagnostic variableMapMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mora_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mora_checker_rejection_no_claim
    {checkerRejection publicClaim : Prop} :
    checkerRejection ->
    (checkerRejection -> publicClaim -> False) ->
    AyMORANoClaimDiagnostic checkerRejection publicClaim :=
  fun hreject hblocks =>
    ay_mora_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_mora_exit_code_mismatch_no_claim
    {exitCodeMismatch publicClaim : Prop} :
    exitCodeMismatch ->
    (exitCodeMismatch -> publicClaim -> False) ->
    AyMORANoClaimDiagnostic exitCodeMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mora_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mora_fingerprint_mismatch_no_claim
    {fingerprintMismatch publicClaim : Prop} :
    fingerprintMismatch ->
    (fingerprintMismatch -> publicClaim -> False) ->
    AyMORANoClaimDiagnostic fingerprintMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_mora_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_mora_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMORANoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_mora_no_claim_diagnostic_blocks h hclaim

theorem ay_mora_bad_archive_no_stale_sat_validation
    {missingArchiveEntry staleOutputDigest variableMapMismatch
      checkerRejection exitCodeMismatch fingerprintMismatch publicClaim :
      Prop} :
    (missingArchiveEntry -> publicClaim -> False) ->
    (staleOutputDigest -> publicClaim -> False) ->
    (variableMapMismatch -> publicClaim -> False) ->
    (checkerRejection -> publicClaim -> False) ->
    (exitCodeMismatch -> publicClaim -> False) ->
    (fingerprintMismatch -> publicClaim -> False) ->
    AyMORAConj
      (missingArchiveEntry ->
        AyMORANoClaimDiagnostic missingArchiveEntry publicClaim)
      (AyMORAConj
        (staleOutputDigest ->
          AyMORANoClaimDiagnostic staleOutputDigest publicClaim)
        (AyMORAConj
          (variableMapMismatch ->
            AyMORANoClaimDiagnostic variableMapMismatch publicClaim)
          (AyMORAConj
            (checkerRejection ->
              AyMORANoClaimDiagnostic checkerRejection publicClaim)
            (AyMORAConj
              (exitCodeMismatch ->
                AyMORANoClaimDiagnostic exitCodeMismatch publicClaim)
              (fingerprintMismatch ->
                AyMORANoClaimDiagnostic
                  fingerprintMismatch publicClaim))))) :=
  fun hmissing hdigest hmap hchecker hexit hfingerprint =>
    ay_mora_conj_intro
      (fun h => ay_mora_missing_archive_entry_no_claim h hmissing)
      (ay_mora_conj_intro
        (fun h => ay_mora_stale_output_digest_no_claim h hdigest)
        (ay_mora_conj_intro
          (fun h => ay_mora_variable_map_mismatch_no_claim h hmap)
          (ay_mora_conj_intro
            (fun h => ay_mora_checker_rejection_no_claim h hchecker)
            (ay_mora_conj_intro
              (fun h => ay_mora_exit_code_mismatch_no_claim h hexit)
              (fun h =>
                ay_mora_fingerprint_mismatch_no_claim h hfingerprint)))))
