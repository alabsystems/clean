-- SAT-COMP/ay SAT assignment output-format guard soundness skeleton.
-- A canonical assignment may be emitted only when ordering, completeness,
-- DIMACS mapping, eliminated defaults, checker replay, digest, and exit-code
-- evidence all agree.

def AyMAOFConj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> right -> goal) -> goal

def AyMAOFDisj (left right : Prop) : Prop :=
  ∀ goal : Prop, (left -> goal) -> (right -> goal) -> goal

def AyMAOFEquisat (left right : Prop) : Prop :=
  AyMAOFConj (left -> right) (right -> left)

def AyMAOFVariableOrdering
    (canonicalOrder noDuplicates strictlyOrdered : Prop) : Prop :=
  AyMAOFConj canonicalOrder (AyMAOFConj noDuplicates strictlyOrdered)

def AyMAOFDomainCompleteness
    (allVisibleVariables assignedVariables noMissingVariables : Prop) : Prop :=
  AyMAOFConj allVisibleVariables
    (AyMAOFConj assignedVariables noMissingVariables)

def AyMAOFDIMACSVariableMap
    (dimacsMap originalVariableMap mapFresh : Prop) : Prop :=
  AyMAOFConj dimacsMap (AyMAOFConj originalVariableMap mapFresh)

def AyMAOFEliminatedDefaults
    (eliminatedVariables defaultAssignments defaultsComplete : Prop) : Prop :=
  AyMAOFConj eliminatedVariables
    (AyMAOFConj defaultAssignments defaultsComplete)

def AyMAOFModelCheckerReplay (checkerAccepted replayTrace : Prop) : Prop :=
  AyMAOFConj checkerAccepted replayTrace

def AyMAOFManifestDigest
    (manifestEntry outputDigest digestAgreement : Prop) : Prop :=
  AyMAOFConj manifestEntry (AyMAOFConj outputDigest digestAgreement)

def AyMAOFExitCodeContract
    (satExitCode stdoutContract noErrorExit : Prop) : Prop :=
  AyMAOFConj satExitCode (AyMAOFConj stdoutContract noErrorExit)

def AyMAOFOutputGuardEvidence
    (orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk :
      Prop) : Prop :=
  AyMAOFConj orderingOk
    (AyMAOFConj completenessOk
      (AyMAOFConj mapOk
        (AyMAOFConj defaultsOk
          (AyMAOFConj checkerOk
            (AyMAOFConj digestOk exitOk)))))

def AyMAOFSatOutputPublication
    (guardEvidence auditEntry publicSatOutput : Prop) : Prop :=
  AyMAOFConj guardEvidence (AyMAOFConj auditEntry publicSatOutput)

def AyMAOFNoClaimDiagnostic (diagnostic publicClaim : Prop) : Prop :=
  AyMAOFConj diagnostic (publicClaim -> False)

def AyMAOFRecomputeObligation (reason recomputeRequest : Prop) : Prop :=
  AyMAOFConj reason recomputeRequest

theorem ay_maof_conj_intro {left right : Prop} :
    left -> right -> AyMAOFConj left right :=
  fun hleft hright goal build => build hleft hright

theorem ay_maof_conj_left {left right : Prop} :
    AyMAOFConj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_maof_conj_right {left right : Prop} :
    AyMAOFConj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_maof_disj_left {left right : Prop} :
    left -> AyMAOFDisj left right :=
  fun hleft goal onLeft _ => onLeft hleft

theorem ay_maof_disj_right {left right : Prop} :
    right -> AyMAOFDisj left right :=
  fun hright goal _ onRight => onRight hright

theorem ay_maof_equisat_intro {left right : Prop} :
    (left -> right) -> (right -> left) -> AyMAOFEquisat left right :=
  fun hf hb => ay_maof_conj_intro hf hb

theorem ay_maof_equisat_forward {left right : Prop} :
    AyMAOFEquisat left right -> left -> right :=
  fun h => ay_maof_conj_left h

theorem ay_maof_equisat_backward {left right : Prop} :
    AyMAOFEquisat left right -> right -> left :=
  fun h => ay_maof_conj_right h

theorem ay_maof_variable_ordering_intro
    {canonicalOrder noDuplicates strictlyOrdered : Prop} :
    canonicalOrder ->
    noDuplicates ->
    strictlyOrdered ->
    AyMAOFVariableOrdering canonicalOrder noDuplicates strictlyOrdered :=
  fun horder hnodup hstrict =>
    ay_maof_conj_intro horder (ay_maof_conj_intro hnodup hstrict)

theorem ay_maof_variable_ordering_order
    {canonicalOrder noDuplicates strictlyOrdered : Prop} :
    AyMAOFVariableOrdering canonicalOrder noDuplicates strictlyOrdered ->
    canonicalOrder :=
  fun h => ay_maof_conj_left h

theorem ay_maof_variable_ordering_no_duplicates
    {canonicalOrder noDuplicates strictlyOrdered : Prop} :
    AyMAOFVariableOrdering canonicalOrder noDuplicates strictlyOrdered ->
    noDuplicates :=
  fun h => ay_maof_conj_left (ay_maof_conj_right h)

theorem ay_maof_variable_ordering_strict
    {canonicalOrder noDuplicates strictlyOrdered : Prop} :
    AyMAOFVariableOrdering canonicalOrder noDuplicates strictlyOrdered ->
    strictlyOrdered :=
  fun h => ay_maof_conj_right (ay_maof_conj_right h)

theorem ay_maof_domain_completeness_intro
    {allVisibleVariables assignedVariables noMissingVariables : Prop} :
    allVisibleVariables ->
    assignedVariables ->
    noMissingVariables ->
    AyMAOFDomainCompleteness
      allVisibleVariables assignedVariables noMissingVariables :=
  fun hall hassigned hmissing =>
    ay_maof_conj_intro hall (ay_maof_conj_intro hassigned hmissing)

theorem ay_maof_domain_completeness_all
    {allVisibleVariables assignedVariables noMissingVariables : Prop} :
    AyMAOFDomainCompleteness
      allVisibleVariables assignedVariables noMissingVariables ->
    allVisibleVariables :=
  fun h => ay_maof_conj_left h

theorem ay_maof_domain_completeness_assigned
    {allVisibleVariables assignedVariables noMissingVariables : Prop} :
    AyMAOFDomainCompleteness
      allVisibleVariables assignedVariables noMissingVariables ->
    assignedVariables :=
  fun h => ay_maof_conj_left (ay_maof_conj_right h)

theorem ay_maof_domain_completeness_no_missing
    {allVisibleVariables assignedVariables noMissingVariables : Prop} :
    AyMAOFDomainCompleteness
      allVisibleVariables assignedVariables noMissingVariables ->
    noMissingVariables :=
  fun h => ay_maof_conj_right (ay_maof_conj_right h)

theorem ay_maof_dimacs_variable_map_intro
    {dimacsMap originalVariableMap mapFresh : Prop} :
    dimacsMap ->
    originalVariableMap ->
    mapFresh ->
    AyMAOFDIMACSVariableMap dimacsMap originalVariableMap mapFresh :=
  fun hdimacs horiginal hfresh =>
    ay_maof_conj_intro hdimacs (ay_maof_conj_intro horiginal hfresh)

theorem ay_maof_dimacs_variable_map_dimacs
    {dimacsMap originalVariableMap mapFresh : Prop} :
    AyMAOFDIMACSVariableMap dimacsMap originalVariableMap mapFresh ->
    dimacsMap :=
  fun h => ay_maof_conj_left h

theorem ay_maof_dimacs_variable_map_original
    {dimacsMap originalVariableMap mapFresh : Prop} :
    AyMAOFDIMACSVariableMap dimacsMap originalVariableMap mapFresh ->
    originalVariableMap :=
  fun h => ay_maof_conj_left (ay_maof_conj_right h)

theorem ay_maof_dimacs_variable_map_fresh
    {dimacsMap originalVariableMap mapFresh : Prop} :
    AyMAOFDIMACSVariableMap dimacsMap originalVariableMap mapFresh ->
    mapFresh :=
  fun h => ay_maof_conj_right (ay_maof_conj_right h)

theorem ay_maof_eliminated_defaults_intro
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    eliminatedVariables ->
    defaultAssignments ->
    defaultsComplete ->
    AyMAOFEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete :=
  fun helim hdefaults hcomplete =>
    ay_maof_conj_intro helim
      (ay_maof_conj_intro hdefaults hcomplete)

theorem ay_maof_eliminated_defaults_variables
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMAOFEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    eliminatedVariables :=
  fun h => ay_maof_conj_left h

theorem ay_maof_eliminated_defaults_assignments
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMAOFEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    defaultAssignments :=
  fun h => ay_maof_conj_left (ay_maof_conj_right h)

theorem ay_maof_eliminated_defaults_complete
    {eliminatedVariables defaultAssignments defaultsComplete : Prop} :
    AyMAOFEliminatedDefaults
      eliminatedVariables defaultAssignments defaultsComplete ->
    defaultsComplete :=
  fun h => ay_maof_conj_right (ay_maof_conj_right h)

theorem ay_maof_model_checker_replay_intro
    {checkerAccepted replayTrace : Prop} :
    checkerAccepted ->
    replayTrace ->
    AyMAOFModelCheckerReplay checkerAccepted replayTrace :=
  fun haccepted htrace => ay_maof_conj_intro haccepted htrace

theorem ay_maof_model_checker_replay_accepted
    {checkerAccepted replayTrace : Prop} :
    AyMAOFModelCheckerReplay checkerAccepted replayTrace ->
    checkerAccepted :=
  fun h => ay_maof_conj_left h

theorem ay_maof_model_checker_replay_trace
    {checkerAccepted replayTrace : Prop} :
    AyMAOFModelCheckerReplay checkerAccepted replayTrace ->
    replayTrace :=
  fun h => ay_maof_conj_right h

theorem ay_maof_manifest_digest_intro
    {manifestEntry outputDigest digestAgreement : Prop} :
    manifestEntry ->
    outputDigest ->
    digestAgreement ->
    AyMAOFManifestDigest manifestEntry outputDigest digestAgreement :=
  fun hmanifest hdigest hagree =>
    ay_maof_conj_intro hmanifest
      (ay_maof_conj_intro hdigest hagree)

theorem ay_maof_manifest_digest_entry
    {manifestEntry outputDigest digestAgreement : Prop} :
    AyMAOFManifestDigest manifestEntry outputDigest digestAgreement ->
    manifestEntry :=
  fun h => ay_maof_conj_left h

theorem ay_maof_manifest_digest_output
    {manifestEntry outputDigest digestAgreement : Prop} :
    AyMAOFManifestDigest manifestEntry outputDigest digestAgreement ->
    outputDigest :=
  fun h => ay_maof_conj_left (ay_maof_conj_right h)

theorem ay_maof_manifest_digest_agreement
    {manifestEntry outputDigest digestAgreement : Prop} :
    AyMAOFManifestDigest manifestEntry outputDigest digestAgreement ->
    digestAgreement :=
  fun h => ay_maof_conj_right (ay_maof_conj_right h)

theorem ay_maof_exit_code_contract_intro
    {satExitCode stdoutContract noErrorExit : Prop} :
    satExitCode ->
    stdoutContract ->
    noErrorExit ->
    AyMAOFExitCodeContract satExitCode stdoutContract noErrorExit :=
  fun hexit hstdout hnoerror =>
    ay_maof_conj_intro hexit (ay_maof_conj_intro hstdout hnoerror)

theorem ay_maof_exit_code_contract_sat
    {satExitCode stdoutContract noErrorExit : Prop} :
    AyMAOFExitCodeContract satExitCode stdoutContract noErrorExit ->
    satExitCode :=
  fun h => ay_maof_conj_left h

theorem ay_maof_exit_code_contract_stdout
    {satExitCode stdoutContract noErrorExit : Prop} :
    AyMAOFExitCodeContract satExitCode stdoutContract noErrorExit ->
    stdoutContract :=
  fun h => ay_maof_conj_left (ay_maof_conj_right h)

theorem ay_maof_exit_code_contract_no_error
    {satExitCode stdoutContract noErrorExit : Prop} :
    AyMAOFExitCodeContract satExitCode stdoutContract noErrorExit ->
    noErrorExit :=
  fun h => ay_maof_conj_right (ay_maof_conj_right h)

theorem ay_maof_output_guard_evidence_intro
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk :
      Prop} :
    orderingOk ->
    completenessOk ->
    mapOk ->
    defaultsOk ->
    checkerOk ->
    digestOk ->
    exitOk ->
    AyMAOFOutputGuardEvidence
      orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk :=
  fun horder hcomplete hmap hdefaults hchecker hdigest hexit =>
    ay_maof_conj_intro horder
      (ay_maof_conj_intro hcomplete
        (ay_maof_conj_intro hmap
          (ay_maof_conj_intro hdefaults
            (ay_maof_conj_intro hchecker
              (ay_maof_conj_intro hdigest hexit)))))

theorem ay_maof_output_guard_evidence_ordering
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk :
      Prop} :
    AyMAOFOutputGuardEvidence
      orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk ->
    orderingOk :=
  fun h => ay_maof_conj_left h

theorem ay_maof_output_guard_evidence_completeness
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk :
      Prop} :
    AyMAOFOutputGuardEvidence
      orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk ->
    completenessOk :=
  fun h => ay_maof_conj_left (ay_maof_conj_right h)

theorem ay_maof_output_guard_evidence_map
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk :
      Prop} :
    AyMAOFOutputGuardEvidence
      orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk ->
    mapOk :=
  fun h => ay_maof_conj_left (ay_maof_conj_right (ay_maof_conj_right h))

theorem ay_maof_output_guard_evidence_defaults
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk :
      Prop} :
    AyMAOFOutputGuardEvidence
      orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk ->
    defaultsOk :=
  fun h =>
    ay_maof_conj_left
      (ay_maof_conj_right (ay_maof_conj_right (ay_maof_conj_right h)))

theorem ay_maof_output_guard_evidence_checker
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk :
      Prop} :
    AyMAOFOutputGuardEvidence
      orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk ->
    checkerOk :=
  fun h =>
    ay_maof_conj_left
      (ay_maof_conj_right
        (ay_maof_conj_right (ay_maof_conj_right (ay_maof_conj_right h))))

theorem ay_maof_output_guard_evidence_digest
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk :
      Prop} :
    AyMAOFOutputGuardEvidence
      orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk ->
    digestOk :=
  fun h =>
    ay_maof_conj_left
      (ay_maof_conj_right
        (ay_maof_conj_right
          (ay_maof_conj_right (ay_maof_conj_right (ay_maof_conj_right h)))))

theorem ay_maof_output_guard_evidence_exit
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk :
      Prop} :
    AyMAOFOutputGuardEvidence
      orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk ->
    exitOk :=
  fun h =>
    ay_maof_conj_right
      (ay_maof_conj_right
        (ay_maof_conj_right
          (ay_maof_conj_right (ay_maof_conj_right (ay_maof_conj_right h)))))

theorem ay_maof_sat_output_publication_intro
    {guardEvidence auditEntry publicSatOutput : Prop} :
    guardEvidence ->
    auditEntry ->
    publicSatOutput ->
    AyMAOFSatOutputPublication guardEvidence auditEntry publicSatOutput :=
  fun hevidence haudit houtput =>
    ay_maof_conj_intro hevidence (ay_maof_conj_intro haudit houtput)

theorem ay_maof_sat_output_publication_evidence
    {guardEvidence auditEntry publicSatOutput : Prop} :
    AyMAOFSatOutputPublication guardEvidence auditEntry publicSatOutput ->
    guardEvidence :=
  fun h => ay_maof_conj_left h

theorem ay_maof_sat_output_publication_audit
    {guardEvidence auditEntry publicSatOutput : Prop} :
    AyMAOFSatOutputPublication guardEvidence auditEntry publicSatOutput ->
    auditEntry :=
  fun h => ay_maof_conj_left (ay_maof_conj_right h)

theorem ay_maof_sat_output_publication_output
    {guardEvidence auditEntry publicSatOutput : Prop} :
    AyMAOFSatOutputPublication guardEvidence auditEntry publicSatOutput ->
    publicSatOutput :=
  fun h => ay_maof_conj_right (ay_maof_conj_right h)

theorem ay_maof_accepted_output_preserves_sat_publication
    {guardEvidence auditEntry publicSatOutput : Prop} :
    AyMAOFSatOutputPublication guardEvidence auditEntry publicSatOutput ->
    publicSatOutput :=
  fun h => ay_maof_sat_output_publication_output h

theorem ay_maof_publication_requires_ordering
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMAOFSatOutputPublication
      (AyMAOFOutputGuardEvidence
        orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    orderingOk :=
  fun h =>
    ay_maof_output_guard_evidence_ordering
      (ay_maof_sat_output_publication_evidence h)

theorem ay_maof_publication_requires_completeness
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMAOFSatOutputPublication
      (AyMAOFOutputGuardEvidence
        orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    completenessOk :=
  fun h =>
    ay_maof_output_guard_evidence_completeness
      (ay_maof_sat_output_publication_evidence h)

theorem ay_maof_publication_requires_map
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMAOFSatOutputPublication
      (AyMAOFOutputGuardEvidence
        orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    mapOk :=
  fun h =>
    ay_maof_output_guard_evidence_map
      (ay_maof_sat_output_publication_evidence h)

theorem ay_maof_publication_requires_defaults
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMAOFSatOutputPublication
      (AyMAOFOutputGuardEvidence
        orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    defaultsOk :=
  fun h =>
    ay_maof_output_guard_evidence_defaults
      (ay_maof_sat_output_publication_evidence h)

theorem ay_maof_publication_requires_checker
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMAOFSatOutputPublication
      (AyMAOFOutputGuardEvidence
        orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    checkerOk :=
  fun h =>
    ay_maof_output_guard_evidence_checker
      (ay_maof_sat_output_publication_evidence h)

theorem ay_maof_publication_requires_digest
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMAOFSatOutputPublication
      (AyMAOFOutputGuardEvidence
        orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    digestOk :=
  fun h =>
    ay_maof_output_guard_evidence_digest
      (ay_maof_sat_output_publication_evidence h)

theorem ay_maof_publication_requires_exit_contract
    {orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk
      auditEntry publicSatOutput : Prop} :
    AyMAOFSatOutputPublication
      (AyMAOFOutputGuardEvidence
        orderingOk completenessOk mapOk defaultsOk checkerOk digestOk exitOk)
      auditEntry
      publicSatOutput ->
    exitOk :=
  fun h =>
    ay_maof_output_guard_evidence_exit
      (ay_maof_sat_output_publication_evidence h)

theorem ay_maof_sat_output_publication_sound_exact
    {guardEvidence auditEntry publicSatOutput : Prop} :
    AyMAOFEquisat
      (AyMAOFSatOutputPublication guardEvidence auditEntry publicSatOutput)
      (AyMAOFConj guardEvidence
        (AyMAOFConj auditEntry publicSatOutput)) :=
  ay_maof_equisat_intro
    (fun h => h)
    (fun h => h)

theorem ay_maof_no_claim_diagnostic_intro
    {diagnostic publicClaim : Prop} :
    diagnostic ->
    (publicClaim -> False) ->
    AyMAOFNoClaimDiagnostic diagnostic publicClaim :=
  fun hdiagnostic hblocks => ay_maof_conj_intro hdiagnostic hblocks

theorem ay_maof_no_claim_diagnostic_reason
    {diagnostic publicClaim : Prop} :
    AyMAOFNoClaimDiagnostic diagnostic publicClaim ->
    diagnostic :=
  fun h => ay_maof_conj_left h

theorem ay_maof_no_claim_diagnostic_blocks
    {diagnostic publicClaim : Prop} :
    AyMAOFNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h => ay_maof_conj_right h

theorem ay_maof_recompute_obligation_intro
    {reason recomputeRequest : Prop} :
    reason ->
    recomputeRequest ->
    AyMAOFRecomputeObligation reason recomputeRequest :=
  fun hreason hrequest => ay_maof_conj_intro hreason hrequest

theorem ay_maof_recompute_obligation_reason
    {reason recomputeRequest : Prop} :
    AyMAOFRecomputeObligation reason recomputeRequest ->
    reason :=
  fun h => ay_maof_conj_left h

theorem ay_maof_recompute_obligation_request
    {reason recomputeRequest : Prop} :
    AyMAOFRecomputeObligation reason recomputeRequest ->
    recomputeRequest :=
  fun h => ay_maof_conj_right h

theorem ay_maof_missing_variables_recompute
    {missingVariables recomputeRequest : Prop} :
    missingVariables ->
    recomputeRequest ->
    AyMAOFRecomputeObligation missingVariables recomputeRequest :=
  fun hmissing hrecompute =>
    ay_maof_recompute_obligation_intro hmissing hrecompute

theorem ay_maof_missing_variables_no_claim
    {missingVariables publicClaim : Prop} :
    missingVariables ->
    (missingVariables -> publicClaim -> False) ->
    AyMAOFNoClaimDiagnostic missingVariables publicClaim :=
  fun hmissing hblocks =>
    ay_maof_no_claim_diagnostic_intro hmissing (hblocks hmissing)

theorem ay_maof_duplicate_or_misordered_literals_no_claim
    {duplicateOrMisorderedLiterals publicClaim : Prop} :
    duplicateOrMisorderedLiterals ->
    (duplicateOrMisorderedLiterals -> publicClaim -> False) ->
    AyMAOFNoClaimDiagnostic duplicateOrMisorderedLiterals publicClaim :=
  fun hbad hblocks =>
    ay_maof_no_claim_diagnostic_intro hbad (hblocks hbad)

theorem ay_maof_stale_map_no_claim
    {staleMap publicClaim : Prop} :
    staleMap ->
    (staleMap -> publicClaim -> False) ->
    AyMAOFNoClaimDiagnostic staleMap publicClaim :=
  fun hstale hblocks =>
    ay_maof_no_claim_diagnostic_intro hstale (hblocks hstale)

theorem ay_maof_digest_mismatch_no_claim
    {digestMismatch publicClaim : Prop} :
    digestMismatch ->
    (digestMismatch -> publicClaim -> False) ->
    AyMAOFNoClaimDiagnostic digestMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_maof_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_maof_checker_rejection_no_claim
    {checkerRejection publicClaim : Prop} :
    checkerRejection ->
    (checkerRejection -> publicClaim -> False) ->
    AyMAOFNoClaimDiagnostic checkerRejection publicClaim :=
  fun hreject hblocks =>
    ay_maof_no_claim_diagnostic_intro hreject (hblocks hreject)

theorem ay_maof_exit_contract_mismatch_no_claim
    {exitContractMismatch publicClaim : Prop} :
    exitContractMismatch ->
    (exitContractMismatch -> publicClaim -> False) ->
    AyMAOFNoClaimDiagnostic exitContractMismatch publicClaim :=
  fun hmismatch hblocks =>
    ay_maof_no_claim_diagnostic_intro hmismatch (hblocks hmismatch)

theorem ay_maof_diagnostic_blocks_public_claim
    {diagnostic publicClaim : Prop} :
    AyMAOFNoClaimDiagnostic diagnostic publicClaim ->
    publicClaim ->
    False :=
  fun h hclaim => ay_maof_no_claim_diagnostic_blocks h hclaim

theorem ay_maof_bad_output_format_no_stale_sat_emission
    {missingVariables duplicateOrMisorderedLiterals staleMap digestMismatch
      checkerRejection exitContractMismatch publicClaim : Prop} :
    (missingVariables -> publicClaim -> False) ->
    (duplicateOrMisorderedLiterals -> publicClaim -> False) ->
    (staleMap -> publicClaim -> False) ->
    (digestMismatch -> publicClaim -> False) ->
    (checkerRejection -> publicClaim -> False) ->
    (exitContractMismatch -> publicClaim -> False) ->
    AyMAOFConj
      (missingVariables ->
        AyMAOFNoClaimDiagnostic missingVariables publicClaim)
      (AyMAOFConj
        (duplicateOrMisorderedLiterals ->
          AyMAOFNoClaimDiagnostic
            duplicateOrMisorderedLiterals publicClaim)
        (AyMAOFConj
          (staleMap -> AyMAOFNoClaimDiagnostic staleMap publicClaim)
          (AyMAOFConj
            (digestMismatch ->
              AyMAOFNoClaimDiagnostic digestMismatch publicClaim)
            (AyMAOFConj
              (checkerRejection ->
                AyMAOFNoClaimDiagnostic checkerRejection publicClaim)
              (exitContractMismatch ->
                AyMAOFNoClaimDiagnostic
                  exitContractMismatch publicClaim))))) :=
  fun hmissing horder hmap hdigest hchecker hexit =>
    ay_maof_conj_intro
      (fun h => ay_maof_missing_variables_no_claim h hmissing)
      (ay_maof_conj_intro
        (fun h =>
          ay_maof_duplicate_or_misordered_literals_no_claim h horder)
        (ay_maof_conj_intro
          (fun h => ay_maof_stale_map_no_claim h hmap)
          (ay_maof_conj_intro
            (fun h => ay_maof_digest_mismatch_no_claim h hdigest)
            (ay_maof_conj_intro
              (fun h => ay_maof_checker_rejection_no_claim h hchecker)
              (fun h => ay_maof_exit_contract_mismatch_no_claim h hexit)))))
