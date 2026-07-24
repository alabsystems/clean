-- SAT-COMP validator track-rule guard core.
--
-- Public SAT/UNSAT claims are valid for sequential main-track publication only
-- when track, run, configuration, benchmark, input, output, checker, build,
-- archive, fallback, and audit evidence agree.

def ay_trkg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_trkg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_trkg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_trkg_disj satFact (ay_trkg_disj unsatFact noClaimFact)

def ay_trkg_track_contract
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      benchmarkIdentityFingerprint normalizedInputDigest solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (competitionTrackManifest -> sequentialRunManifest ->
      solverConfigurationDigest -> benchmarkIdentityFingerprint ->
      normalizedInputDigest -> solverOutputDigest -> checkerTranscript ->
      solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
      auditTranscript -> result) ->
    result

def ay_trkg_sat_publication
    (trackContract sequentialMainRules checkedModel originalBenchmarkSat :
      Prop) : Prop :=
  ay_trkg_conj trackContract
    (ay_trkg_conj sequentialMainRules
      (ay_trkg_conj checkedModel originalBenchmarkSat))

def ay_trkg_unsat_publication
    (trackContract sequentialMainRules checkedProof originalBenchmarkUnsat :
      Prop) : Prop :=
  ay_trkg_conj trackContract
    (ay_trkg_conj sequentialMainRules
      (ay_trkg_conj checkedProof originalBenchmarkUnsat))

def ay_trkg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_trkg_conj reason (ay_trkg_conj fallbackPath auditTrail)

def ay_trkg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_trkg_conj reason
    (ay_trkg_conj (satFact -> False) (unsatFact -> False))

def ay_trkg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_trkg_conj reason
    (ay_trkg_conj fallbackPath recomputeObligation)

def ay_trkg_track_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_trkg_conj
    (ay_trkg_blocked_publication satFact unsatFact reason)
    (ay_trkg_recompute reason fallbackPath recomputeObligation)

theorem ay_trkg_conj_intro (left right : Prop) :
    left -> right -> ay_trkg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_trkg_conj_left (left right : Prop) :
    ay_trkg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_trkg_conj_right (left right : Prop) :
    ay_trkg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_trkg_disj_left (left right : Prop) :
    left -> ay_trkg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_trkg_disj_right (left right : Prop) :
    right -> ay_trkg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_trkg_track_contract_intro
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      benchmarkIdentityFingerprint normalizedInputDigest solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    competitionTrackManifest -> sequentialRunManifest ->
    solverConfigurationDigest -> benchmarkIdentityFingerprint ->
    normalizedInputDigest -> solverOutputDigest -> checkerTranscript ->
    solverBuildEvidence -> archiveManifest -> fallbackNoClaimPath ->
    auditTranscript ->
    ay_trkg_track_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest benchmarkIdentityFingerprint
      normalizedInputDigest solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :=
  fun trackProof runProof configProof benchmarkProof inputProof outputProof
      checkerProof buildProof archiveProof fallbackProof auditProof result
      build =>
    build trackProof runProof configProof benchmarkProof inputProof outputProof
      checkerProof buildProof archiveProof fallbackProof auditProof

theorem ay_trkg_contract_track
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      benchmarkIdentityFingerprint normalizedInputDigest solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_trkg_track_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest benchmarkIdentityFingerprint
      normalizedInputDigest solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    competitionTrackManifest :=
  fun contract =>
    contract competitionTrackManifest
      (fun trackProof _runProof _configProof _benchmarkProof _inputProof
          _outputProof _checkerProof _buildProof _archiveProof _fallbackProof
          _auditProof => trackProof)

theorem ay_trkg_contract_sequential_run
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      benchmarkIdentityFingerprint normalizedInputDigest solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_trkg_track_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest benchmarkIdentityFingerprint
      normalizedInputDigest solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    sequentialRunManifest :=
  fun contract =>
    contract sequentialRunManifest
      (fun _trackProof runProof _configProof _benchmarkProof _inputProof
          _outputProof _checkerProof _buildProof _archiveProof _fallbackProof
          _auditProof => runProof)

theorem ay_trkg_contract_config
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      benchmarkIdentityFingerprint normalizedInputDigest solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_trkg_track_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest benchmarkIdentityFingerprint
      normalizedInputDigest solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    solverConfigurationDigest :=
  fun contract =>
    contract solverConfigurationDigest
      (fun _trackProof _runProof configProof _benchmarkProof _inputProof
          _outputProof _checkerProof _buildProof _archiveProof _fallbackProof
          _auditProof => configProof)

theorem ay_trkg_contract_benchmark
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      benchmarkIdentityFingerprint normalizedInputDigest solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_trkg_track_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest benchmarkIdentityFingerprint
      normalizedInputDigest solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    benchmarkIdentityFingerprint :=
  fun contract =>
    contract benchmarkIdentityFingerprint
      (fun _trackProof _runProof _configProof benchmarkProof _inputProof
          _outputProof _checkerProof _buildProof _archiveProof _fallbackProof
          _auditProof => benchmarkProof)

theorem ay_trkg_contract_input
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      benchmarkIdentityFingerprint normalizedInputDigest solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_trkg_track_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest benchmarkIdentityFingerprint
      normalizedInputDigest solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    normalizedInputDigest :=
  fun contract =>
    contract normalizedInputDigest
      (fun _trackProof _runProof _configProof _benchmarkProof inputProof
          _outputProof _checkerProof _buildProof _archiveProof _fallbackProof
          _auditProof => inputProof)

theorem ay_trkg_contract_output
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      benchmarkIdentityFingerprint normalizedInputDigest solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_trkg_track_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest benchmarkIdentityFingerprint
      normalizedInputDigest solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    solverOutputDigest :=
  fun contract =>
    contract solverOutputDigest
      (fun _trackProof _runProof _configProof _benchmarkProof _inputProof
          outputProof _checkerProof _buildProof _archiveProof _fallbackProof
          _auditProof => outputProof)

theorem ay_trkg_contract_checker
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      benchmarkIdentityFingerprint normalizedInputDigest solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_trkg_track_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest benchmarkIdentityFingerprint
      normalizedInputDigest solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _trackProof _runProof _configProof _benchmarkProof _inputProof
          _outputProof checkerProof _buildProof _archiveProof _fallbackProof
          _auditProof => checkerProof)

theorem ay_trkg_contract_build
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      benchmarkIdentityFingerprint normalizedInputDigest solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_trkg_track_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest benchmarkIdentityFingerprint
      normalizedInputDigest solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _trackProof _runProof _configProof _benchmarkProof _inputProof
          _outputProof _checkerProof buildProof _archiveProof _fallbackProof
          _auditProof => buildProof)

theorem ay_trkg_contract_archive
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      benchmarkIdentityFingerprint normalizedInputDigest solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_trkg_track_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest benchmarkIdentityFingerprint
      normalizedInputDigest solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _trackProof _runProof _configProof _benchmarkProof _inputProof
          _outputProof _checkerProof _buildProof archiveProof _fallbackProof
          _auditProof => archiveProof)

theorem ay_trkg_contract_fallback
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      benchmarkIdentityFingerprint normalizedInputDigest solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_trkg_track_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest benchmarkIdentityFingerprint
      normalizedInputDigest solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _trackProof _runProof _configProof _benchmarkProof _inputProof
          _outputProof _checkerProof _buildProof _archiveProof fallbackProof
          _auditProof => fallbackProof)

theorem ay_trkg_contract_audit
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      benchmarkIdentityFingerprint normalizedInputDigest solverOutputDigest
      checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_trkg_track_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest benchmarkIdentityFingerprint
      normalizedInputDigest solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _trackProof _runProof _configProof _benchmarkProof _inputProof
          _outputProof _checkerProof _buildProof _archiveProof _fallbackProof
          auditProof => auditProof)

theorem ay_trkg_sat_publication_intro
    (trackContract sequentialMainRules checkedModel originalBenchmarkSat :
      Prop) :
    trackContract -> sequentialMainRules -> checkedModel ->
    originalBenchmarkSat ->
    ay_trkg_sat_publication trackContract sequentialMainRules checkedModel
      originalBenchmarkSat :=
  fun hcontract hrules hchecked horiginal =>
    ay_trkg_conj_intro trackContract
      (ay_trkg_conj sequentialMainRules
        (ay_trkg_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_trkg_conj_intro sequentialMainRules
        (ay_trkg_conj checkedModel originalBenchmarkSat)
        hrules
        (ay_trkg_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_trkg_unsat_publication_intro
    (trackContract sequentialMainRules checkedProof originalBenchmarkUnsat :
      Prop) :
    trackContract -> sequentialMainRules -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_trkg_unsat_publication trackContract sequentialMainRules checkedProof
      originalBenchmarkUnsat :=
  fun hcontract hrules hchecked horiginal =>
    ay_trkg_conj_intro trackContract
      (ay_trkg_conj sequentialMainRules
        (ay_trkg_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_trkg_conj_intro sequentialMainRules
        (ay_trkg_conj checkedProof originalBenchmarkUnsat)
        hrules
        (ay_trkg_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_trkg_sat_publication_original_claim
    (trackContract sequentialMainRules checkedModel originalBenchmarkSat :
      Prop) :
    ay_trkg_sat_publication trackContract sequentialMainRules checkedModel
      originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_trkg_conj_right checkedModel originalBenchmarkSat
      (ay_trkg_conj_right sequentialMainRules
        (ay_trkg_conj checkedModel originalBenchmarkSat)
        (ay_trkg_conj_right trackContract
          (ay_trkg_conj sequentialMainRules
            (ay_trkg_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_trkg_unsat_publication_original_claim
    (trackContract sequentialMainRules checkedProof originalBenchmarkUnsat :
      Prop) :
    ay_trkg_unsat_publication trackContract sequentialMainRules checkedProof
      originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_trkg_conj_right checkedProof originalBenchmarkUnsat
      (ay_trkg_conj_right sequentialMainRules
        (ay_trkg_conj checkedProof originalBenchmarkUnsat)
        (ay_trkg_conj_right trackContract
          (ay_trkg_conj sequentialMainRules
            (ay_trkg_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_trkg_accepted_track_preserves_sat_soundness
    (trackContract sequentialMainRules checkedModel originalBenchmarkSat :
      Prop) :
    ay_trkg_sat_publication trackContract sequentialMainRules checkedModel
      originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_trkg_sat_publication_original_claim trackContract sequentialMainRules
    checkedModel originalBenchmarkSat

theorem ay_trkg_accepted_track_preserves_unsat_soundness
    (trackContract sequentialMainRules checkedProof originalBenchmarkUnsat :
      Prop) :
    ay_trkg_unsat_publication trackContract sequentialMainRules checkedProof
      originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_trkg_unsat_publication_original_claim trackContract sequentialMainRules
    checkedProof originalBenchmarkUnsat

theorem ay_trkg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_trkg_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_trkg_conj_intro reason (ay_trkg_conj fallbackPath auditTrail)
      hreason
      (ay_trkg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_trkg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_trkg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_trkg_conj_intro reason
      (ay_trkg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_trkg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_trkg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_trkg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_trkg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_trkg_conj_right reason
        (ay_trkg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_trkg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_trkg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_trkg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_trkg_conj_right reason
        (ay_trkg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_trkg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_trkg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_trkg_conj_intro reason
      (ay_trkg_conj fallbackPath recomputeObligation)
      hreason
      (ay_trkg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_trkg_track_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_trkg_blocked_publication satFact unsatFact reason ->
    ay_trkg_recompute reason fallbackPath recomputeObligation ->
    ay_trkg_track_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_trkg_conj_intro
      (ay_trkg_blocked_publication satFact unsatFact reason)
      (ay_trkg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_trkg_track_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_trkg_track_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_trkg_blocked_publication_no_sat satFact unsatFact reason
      (ay_trkg_conj_left
        (ay_trkg_blocked_publication satFact unsatFact reason)
        (ay_trkg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_trkg_track_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_trkg_track_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_trkg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_trkg_conj_left
        (ay_trkg_blocked_publication satFact unsatFact reason)
        (ay_trkg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_trkg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_trkg_no_claim reason fallbackPath auditTrail :=
  ay_trkg_no_claim_intro reason fallbackPath auditTrail

theorem ay_trkg_track_mismatch_forces_no_claim
    (trackMismatch fallbackPath auditTrail : Prop) :
    trackMismatch -> fallbackPath -> auditTrail ->
    ay_trkg_no_claim trackMismatch fallbackPath auditTrail :=
  ay_trkg_mismatch_forces_no_claim trackMismatch fallbackPath auditTrail

theorem ay_trkg_config_mismatch_forces_no_claim
    (configMismatch fallbackPath auditTrail : Prop) :
    configMismatch -> fallbackPath -> auditTrail ->
    ay_trkg_no_claim configMismatch fallbackPath auditTrail :=
  ay_trkg_mismatch_forces_no_claim configMismatch fallbackPath auditTrail

theorem ay_trkg_benchmark_mismatch_forces_no_claim
    (benchmarkMismatch fallbackPath auditTrail : Prop) :
    benchmarkMismatch -> fallbackPath -> auditTrail ->
    ay_trkg_no_claim benchmarkMismatch fallbackPath auditTrail :=
  ay_trkg_mismatch_forces_no_claim benchmarkMismatch fallbackPath auditTrail

theorem ay_trkg_input_mismatch_forces_no_claim
    (inputMismatch fallbackPath auditTrail : Prop) :
    inputMismatch -> fallbackPath -> auditTrail ->
    ay_trkg_no_claim inputMismatch fallbackPath auditTrail :=
  ay_trkg_mismatch_forces_no_claim inputMismatch fallbackPath auditTrail

theorem ay_trkg_output_mismatch_forces_no_claim
    (outputMismatch fallbackPath auditTrail : Prop) :
    outputMismatch -> fallbackPath -> auditTrail ->
    ay_trkg_no_claim outputMismatch fallbackPath auditTrail :=
  ay_trkg_mismatch_forces_no_claim outputMismatch fallbackPath auditTrail

theorem ay_trkg_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_trkg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_trkg_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_trkg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_trkg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_trkg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_trkg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_trkg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_trkg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_trkg_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_trkg_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_trkg_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_trkg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_trkg_track_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_trkg_track_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_trkg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_trkg_track_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_trkg_track_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
