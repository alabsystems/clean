-- SAT-COMP validator sequential thread-count guard core.
--
-- Sequential main-track publication is valid only when track, run,
-- configuration, thread-count, runtime transcript, benchmark, output, checker,
-- build, archive, fallback, and audit evidence agree.

def ay_stcg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_stcg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_stcg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_stcg_disj satFact (ay_stcg_disj unsatFact noClaimFact)

def ay_stcg_thread_contract
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (competitionTrackManifest -> sequentialRunManifest ->
      solverConfigurationDigest -> threadCountWitness ->
      runtimeTranscriptDigest -> benchmarkFingerprint -> solverOutputDigest ->
      checkerTranscript -> solverBuildEvidence -> archiveManifest ->
      fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_stcg_sat_publication
    (threadContract sequentialConfiguration checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_stcg_conj threadContract
    (ay_stcg_conj sequentialConfiguration
      (ay_stcg_conj checkedModel originalBenchmarkSat))

def ay_stcg_unsat_publication
    (threadContract sequentialConfiguration checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_stcg_conj threadContract
    (ay_stcg_conj sequentialConfiguration
      (ay_stcg_conj checkedProof originalBenchmarkUnsat))

def ay_stcg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_stcg_conj reason (ay_stcg_conj fallbackPath auditTrail)

def ay_stcg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_stcg_conj reason
    (ay_stcg_conj (satFact -> False) (unsatFact -> False))

def ay_stcg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_stcg_conj reason
    (ay_stcg_conj fallbackPath recomputeObligation)

def ay_stcg_thread_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_stcg_conj
    (ay_stcg_blocked_publication satFact unsatFact reason)
    (ay_stcg_recompute reason fallbackPath recomputeObligation)

theorem ay_stcg_conj_intro (left right : Prop) :
    left -> right -> ay_stcg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_stcg_conj_left (left right : Prop) :
    ay_stcg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_stcg_conj_right (left right : Prop) :
    ay_stcg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_stcg_disj_left (left right : Prop) :
    left -> ay_stcg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_stcg_disj_right (left right : Prop) :
    right -> ay_stcg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_stcg_thread_contract_intro
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    competitionTrackManifest -> sequentialRunManifest ->
    solverConfigurationDigest -> threadCountWitness ->
    runtimeTranscriptDigest -> benchmarkFingerprint -> solverOutputDigest ->
    checkerTranscript -> solverBuildEvidence -> archiveManifest ->
    fallbackNoClaimPath -> auditTranscript ->
    ay_stcg_thread_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest threadCountWitness runtimeTranscriptDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript :=
  fun trackProof runProof configProof threadProof runtimeProof
      benchmarkProof outputProof checkerProof buildProof archiveProof
      fallbackProof auditProof result build =>
    build trackProof runProof configProof threadProof runtimeProof
      benchmarkProof outputProof checkerProof buildProof archiveProof
      fallbackProof auditProof

theorem ay_stcg_contract_track
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_stcg_thread_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest threadCountWitness runtimeTranscriptDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    competitionTrackManifest :=
  fun contract =>
    contract competitionTrackManifest
      (fun trackProof _runProof _configProof _threadProof _runtimeProof
          _benchmarkProof _outputProof _checkerProof _buildProof _archiveProof
          _fallbackProof _auditProof => trackProof)

theorem ay_stcg_contract_sequential_run
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_stcg_thread_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest threadCountWitness runtimeTranscriptDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    sequentialRunManifest :=
  fun contract =>
    contract sequentialRunManifest
      (fun _trackProof runProof _configProof _threadProof _runtimeProof
          _benchmarkProof _outputProof _checkerProof _buildProof _archiveProof
          _fallbackProof _auditProof => runProof)

theorem ay_stcg_contract_config
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_stcg_thread_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest threadCountWitness runtimeTranscriptDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    solverConfigurationDigest :=
  fun contract =>
    contract solverConfigurationDigest
      (fun _trackProof _runProof configProof _threadProof _runtimeProof
          _benchmarkProof _outputProof _checkerProof _buildProof _archiveProof
          _fallbackProof _auditProof => configProof)

theorem ay_stcg_contract_thread_count
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_stcg_thread_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest threadCountWitness runtimeTranscriptDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    threadCountWitness :=
  fun contract =>
    contract threadCountWitness
      (fun _trackProof _runProof _configProof threadProof _runtimeProof
          _benchmarkProof _outputProof _checkerProof _buildProof _archiveProof
          _fallbackProof _auditProof => threadProof)

theorem ay_stcg_contract_runtime_transcript
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_stcg_thread_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest threadCountWitness runtimeTranscriptDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    runtimeTranscriptDigest :=
  fun contract =>
    contract runtimeTranscriptDigest
      (fun _trackProof _runProof _configProof _threadProof runtimeProof
          _benchmarkProof _outputProof _checkerProof _buildProof _archiveProof
          _fallbackProof _auditProof => runtimeProof)

theorem ay_stcg_contract_benchmark
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_stcg_thread_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest threadCountWitness runtimeTranscriptDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _trackProof _runProof _configProof _threadProof _runtimeProof
          benchmarkProof _outputProof _checkerProof _buildProof _archiveProof
          _fallbackProof _auditProof => benchmarkProof)

theorem ay_stcg_contract_output
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_stcg_thread_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest threadCountWitness runtimeTranscriptDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    solverOutputDigest :=
  fun contract =>
    contract solverOutputDigest
      (fun _trackProof _runProof _configProof _threadProof _runtimeProof
          _benchmarkProof outputProof _checkerProof _buildProof _archiveProof
          _fallbackProof _auditProof => outputProof)

theorem ay_stcg_contract_checker
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_stcg_thread_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest threadCountWitness runtimeTranscriptDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _trackProof _runProof _configProof _threadProof _runtimeProof
          _benchmarkProof _outputProof checkerProof _buildProof _archiveProof
          _fallbackProof _auditProof => checkerProof)

theorem ay_stcg_contract_build
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_stcg_thread_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest threadCountWitness runtimeTranscriptDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _trackProof _runProof _configProof _threadProof _runtimeProof
          _benchmarkProof _outputProof _checkerProof buildProof _archiveProof
          _fallbackProof _auditProof => buildProof)

theorem ay_stcg_contract_archive
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_stcg_thread_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest threadCountWitness runtimeTranscriptDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _trackProof _runProof _configProof _threadProof _runtimeProof
          _benchmarkProof _outputProof _checkerProof _buildProof archiveProof
          _fallbackProof _auditProof => archiveProof)

theorem ay_stcg_contract_fallback
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_stcg_thread_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest threadCountWitness runtimeTranscriptDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _trackProof _runProof _configProof _threadProof _runtimeProof
          _benchmarkProof _outputProof _checkerProof _buildProof _archiveProof
          fallbackProof _auditProof => fallbackProof)

theorem ay_stcg_contract_audit
    (competitionTrackManifest sequentialRunManifest solverConfigurationDigest
      threadCountWitness runtimeTranscriptDigest benchmarkFingerprint
      solverOutputDigest checkerTranscript solverBuildEvidence archiveManifest
      fallbackNoClaimPath auditTranscript : Prop) :
    ay_stcg_thread_contract competitionTrackManifest sequentialRunManifest
      solverConfigurationDigest threadCountWitness runtimeTranscriptDigest
      benchmarkFingerprint solverOutputDigest checkerTranscript
      solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _trackProof _runProof _configProof _threadProof _runtimeProof
          _benchmarkProof _outputProof _checkerProof _buildProof _archiveProof
          _fallbackProof auditProof => auditProof)

theorem ay_stcg_sat_publication_intro
    (threadContract sequentialConfiguration checkedModel
      originalBenchmarkSat : Prop) :
    threadContract -> sequentialConfiguration -> checkedModel ->
    originalBenchmarkSat ->
    ay_stcg_sat_publication threadContract sequentialConfiguration
      checkedModel originalBenchmarkSat :=
  fun hcontract hseq hchecked horiginal =>
    ay_stcg_conj_intro threadContract
      (ay_stcg_conj sequentialConfiguration
        (ay_stcg_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_stcg_conj_intro sequentialConfiguration
        (ay_stcg_conj checkedModel originalBenchmarkSat)
        hseq
        (ay_stcg_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_stcg_unsat_publication_intro
    (threadContract sequentialConfiguration checkedProof
      originalBenchmarkUnsat : Prop) :
    threadContract -> sequentialConfiguration -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_stcg_unsat_publication threadContract sequentialConfiguration
      checkedProof originalBenchmarkUnsat :=
  fun hcontract hseq hchecked horiginal =>
    ay_stcg_conj_intro threadContract
      (ay_stcg_conj sequentialConfiguration
        (ay_stcg_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_stcg_conj_intro sequentialConfiguration
        (ay_stcg_conj checkedProof originalBenchmarkUnsat)
        hseq
        (ay_stcg_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_stcg_sat_publication_original_claim
    (threadContract sequentialConfiguration checkedModel
      originalBenchmarkSat : Prop) :
    ay_stcg_sat_publication threadContract sequentialConfiguration
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_stcg_conj_right checkedModel originalBenchmarkSat
      (ay_stcg_conj_right sequentialConfiguration
        (ay_stcg_conj checkedModel originalBenchmarkSat)
        (ay_stcg_conj_right threadContract
          (ay_stcg_conj sequentialConfiguration
            (ay_stcg_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_stcg_unsat_publication_original_claim
    (threadContract sequentialConfiguration checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_stcg_unsat_publication threadContract sequentialConfiguration
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_stcg_conj_right checkedProof originalBenchmarkUnsat
      (ay_stcg_conj_right sequentialConfiguration
        (ay_stcg_conj checkedProof originalBenchmarkUnsat)
        (ay_stcg_conj_right threadContract
          (ay_stcg_conj sequentialConfiguration
            (ay_stcg_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_stcg_accepted_thread_guard_preserves_sat_soundness
    (threadContract sequentialConfiguration checkedModel
      originalBenchmarkSat : Prop) :
    ay_stcg_sat_publication threadContract sequentialConfiguration
      checkedModel originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_stcg_sat_publication_original_claim threadContract
    sequentialConfiguration checkedModel originalBenchmarkSat

theorem ay_stcg_accepted_thread_guard_preserves_unsat_soundness
    (threadContract sequentialConfiguration checkedProof
      originalBenchmarkUnsat : Prop) :
    ay_stcg_unsat_publication threadContract sequentialConfiguration
      checkedProof originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_stcg_unsat_publication_original_claim threadContract
    sequentialConfiguration checkedProof originalBenchmarkUnsat

theorem ay_stcg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_stcg_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_stcg_conj_intro reason (ay_stcg_conj fallbackPath auditTrail)
      hreason
      (ay_stcg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_stcg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_stcg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_stcg_conj_intro reason
      (ay_stcg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_stcg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_stcg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_stcg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_stcg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_stcg_conj_right reason
        (ay_stcg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_stcg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_stcg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_stcg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_stcg_conj_right reason
        (ay_stcg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_stcg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_stcg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_stcg_conj_intro reason
      (ay_stcg_conj fallbackPath recomputeObligation)
      hreason
      (ay_stcg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_stcg_thread_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_stcg_blocked_publication satFact unsatFact reason ->
    ay_stcg_recompute reason fallbackPath recomputeObligation ->
    ay_stcg_thread_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_stcg_conj_intro
      (ay_stcg_blocked_publication satFact unsatFact reason)
      (ay_stcg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_stcg_thread_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_stcg_thread_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_stcg_blocked_publication_no_sat satFact unsatFact reason
      (ay_stcg_conj_left
        (ay_stcg_blocked_publication satFact unsatFact reason)
        (ay_stcg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_stcg_thread_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_stcg_thread_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_stcg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_stcg_conj_left
        (ay_stcg_blocked_publication satFact unsatFact reason)
        (ay_stcg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_stcg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_stcg_no_claim reason fallbackPath auditTrail :=
  ay_stcg_no_claim_intro reason fallbackPath auditTrail

theorem ay_stcg_thread_mismatch_forces_no_claim
    (threadMismatch fallbackPath auditTrail : Prop) :
    threadMismatch -> fallbackPath -> auditTrail ->
    ay_stcg_no_claim threadMismatch fallbackPath auditTrail :=
  ay_stcg_mismatch_forces_no_claim threadMismatch fallbackPath auditTrail

theorem ay_stcg_config_mismatch_forces_no_claim
    (configMismatch fallbackPath auditTrail : Prop) :
    configMismatch -> fallbackPath -> auditTrail ->
    ay_stcg_no_claim configMismatch fallbackPath auditTrail :=
  ay_stcg_mismatch_forces_no_claim configMismatch fallbackPath auditTrail

theorem ay_stcg_track_mismatch_forces_no_claim
    (trackMismatch fallbackPath auditTrail : Prop) :
    trackMismatch -> fallbackPath -> auditTrail ->
    ay_stcg_no_claim trackMismatch fallbackPath auditTrail :=
  ay_stcg_mismatch_forces_no_claim trackMismatch fallbackPath auditTrail

theorem ay_stcg_transcript_mismatch_forces_no_claim
    (transcriptMismatch fallbackPath auditTrail : Prop) :
    transcriptMismatch -> fallbackPath -> auditTrail ->
    ay_stcg_no_claim transcriptMismatch fallbackPath auditTrail :=
  ay_stcg_mismatch_forces_no_claim transcriptMismatch fallbackPath auditTrail

theorem ay_stcg_output_mismatch_forces_no_claim
    (outputMismatch fallbackPath auditTrail : Prop) :
    outputMismatch -> fallbackPath -> auditTrail ->
    ay_stcg_no_claim outputMismatch fallbackPath auditTrail :=
  ay_stcg_mismatch_forces_no_claim outputMismatch fallbackPath auditTrail

theorem ay_stcg_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_stcg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_stcg_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_stcg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_stcg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_stcg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_stcg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_stcg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_stcg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_stcg_fallback_activation_forces_recompute
    (fallbackActivated fallbackPath recomputeObligation : Prop) :
    fallbackActivated -> fallbackPath -> recomputeObligation ->
    ay_stcg_recompute fallbackActivated fallbackPath recomputeObligation :=
  ay_stcg_recompute_intro fallbackActivated fallbackPath recomputeObligation

theorem ay_stcg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_stcg_thread_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_stcg_thread_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_stcg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_stcg_thread_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_stcg_thread_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
