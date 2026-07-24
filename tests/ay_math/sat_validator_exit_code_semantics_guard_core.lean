-- SAT-COMP validator exit-code semantics guard core.
--
-- Exit codes and stdout labels are status evidence, not SAT/UNSAT proof.
-- Public SAT/UNSAT publication requires checker-backed model/proof artifacts.

def ay_ecsg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ecsg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_ecsg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_ecsg_disj satFact (ay_ecsg_disj unsatFact noClaimFact)

def ay_ecsg_exit_contract
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) : Prop :=
  forall result : Prop,
    (benchmarkFingerprint -> solverCommandManifest -> exitCodeTranscript ->
      stdoutStderrDigest -> labelParseTranscript -> modelProofArtifactDigest ->
      checkerTranscript -> resourceNoResultMapping -> solverBuildEvidence ->
      environmentManifest -> archiveManifest -> validatorGate ->
      auditTranscript -> result) ->
    result

def ay_ecsg_sat_publication
    (exitContract checkerBackedArtifact checkedModel originalBenchmarkSat :
      Prop) : Prop :=
  ay_ecsg_conj exitContract
    (ay_ecsg_conj checkerBackedArtifact
      (ay_ecsg_conj checkedModel originalBenchmarkSat))

def ay_ecsg_unsat_publication
    (exitContract checkerBackedArtifact checkedProof originalBenchmarkUnsat :
      Prop) : Prop :=
  ay_ecsg_conj exitContract
    (ay_ecsg_conj checkerBackedArtifact
      (ay_ecsg_conj checkedProof originalBenchmarkUnsat))

def ay_ecsg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_ecsg_conj reason (ay_ecsg_conj fallbackPath auditTrail)

def ay_ecsg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_ecsg_conj reason
    (ay_ecsg_conj (satFact -> False) (unsatFact -> False))

def ay_ecsg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_ecsg_conj reason
    (ay_ecsg_conj fallbackPath recomputeObligation)

def ay_ecsg_exit_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_ecsg_conj
    (ay_ecsg_blocked_publication satFact unsatFact reason)
    (ay_ecsg_recompute reason fallbackPath recomputeObligation)

theorem ay_ecsg_conj_intro (left right : Prop) :
    left -> right -> ay_ecsg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_ecsg_conj_left (left right : Prop) :
    ay_ecsg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_ecsg_conj_right (left right : Prop) :
    ay_ecsg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_ecsg_disj_left (left right : Prop) :
    left -> ay_ecsg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_ecsg_disj_right (left right : Prop) :
    right -> ay_ecsg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_ecsg_exit_contract_intro
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    benchmarkFingerprint -> solverCommandManifest -> exitCodeTranscript ->
    stdoutStderrDigest -> labelParseTranscript -> modelProofArtifactDigest ->
    checkerTranscript -> resourceNoResultMapping -> solverBuildEvidence ->
    environmentManifest -> archiveManifest -> validatorGate ->
    auditTranscript ->
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript :=
  fun benchmarkProof commandProof exitProof streamProof labelProof
      artifactProof checkerProof mappingProof buildProof environmentProof
      archiveProof gateProof auditProof result build =>
    build benchmarkProof commandProof exitProof streamProof labelProof
      artifactProof checkerProof mappingProof buildProof environmentProof
      archiveProof gateProof auditProof

theorem ay_ecsg_contract_benchmark
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun benchmarkProof _commandProof _exitProof _streamProof _labelProof
          _artifactProof _checkerProof _mappingProof _buildProof
          _environmentProof _archiveProof _gateProof _auditProof =>
        benchmarkProof)

theorem ay_ecsg_contract_command
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript ->
    solverCommandManifest :=
  fun contract =>
    contract solverCommandManifest
      (fun _benchmarkProof commandProof _exitProof _streamProof _labelProof
          _artifactProof _checkerProof _mappingProof _buildProof
          _environmentProof _archiveProof _gateProof _auditProof =>
        commandProof)

theorem ay_ecsg_contract_exit
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript ->
    exitCodeTranscript :=
  fun contract =>
    contract exitCodeTranscript
      (fun _benchmarkProof _commandProof exitProof _streamProof _labelProof
          _artifactProof _checkerProof _mappingProof _buildProof
          _environmentProof _archiveProof _gateProof _auditProof => exitProof)

theorem ay_ecsg_contract_stdout_stderr
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript ->
    stdoutStderrDigest :=
  fun contract =>
    contract stdoutStderrDigest
      (fun _benchmarkProof _commandProof _exitProof streamProof _labelProof
          _artifactProof _checkerProof _mappingProof _buildProof
          _environmentProof _archiveProof _gateProof _auditProof =>
        streamProof)

theorem ay_ecsg_contract_label_parse
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript ->
    labelParseTranscript :=
  fun contract =>
    contract labelParseTranscript
      (fun _benchmarkProof _commandProof _exitProof _streamProof labelProof
          _artifactProof _checkerProof _mappingProof _buildProof
          _environmentProof _archiveProof _gateProof _auditProof => labelProof)

theorem ay_ecsg_contract_artifact
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript ->
    modelProofArtifactDigest :=
  fun contract =>
    contract modelProofArtifactDigest
      (fun _benchmarkProof _commandProof _exitProof _streamProof _labelProof
          artifactProof _checkerProof _mappingProof _buildProof
          _environmentProof _archiveProof _gateProof _auditProof =>
        artifactProof)

theorem ay_ecsg_contract_checker
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _benchmarkProof _commandProof _exitProof _streamProof _labelProof
          _artifactProof checkerProof _mappingProof _buildProof
          _environmentProof _archiveProof _gateProof _auditProof =>
        checkerProof)

theorem ay_ecsg_contract_resource_mapping
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript ->
    resourceNoResultMapping :=
  fun contract =>
    contract resourceNoResultMapping
      (fun _benchmarkProof _commandProof _exitProof _streamProof _labelProof
          _artifactProof _checkerProof mappingProof _buildProof
          _environmentProof _archiveProof _gateProof _auditProof =>
        mappingProof)

theorem ay_ecsg_contract_build
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _benchmarkProof _commandProof _exitProof _streamProof _labelProof
          _artifactProof _checkerProof _mappingProof buildProof
          _environmentProof _archiveProof _gateProof _auditProof => buildProof)

theorem ay_ecsg_contract_environment
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript ->
    environmentManifest :=
  fun contract =>
    contract environmentManifest
      (fun _benchmarkProof _commandProof _exitProof _streamProof _labelProof
          _artifactProof _checkerProof _mappingProof _buildProof
          environmentProof _archiveProof _gateProof _auditProof =>
        environmentProof)

theorem ay_ecsg_contract_archive
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _benchmarkProof _commandProof _exitProof _streamProof _labelProof
          _artifactProof _checkerProof _mappingProof _buildProof
          _environmentProof archiveProof _gateProof _auditProof =>
        archiveProof)

theorem ay_ecsg_contract_validator_gate
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript ->
    validatorGate :=
  fun contract =>
    contract validatorGate
      (fun _benchmarkProof _commandProof _exitProof _streamProof _labelProof
          _artifactProof _checkerProof _mappingProof _buildProof
          _environmentProof _archiveProof gateProof _auditProof => gateProof)

theorem ay_ecsg_contract_audit
    (benchmarkFingerprint solverCommandManifest exitCodeTranscript
      stdoutStderrDigest labelParseTranscript modelProofArtifactDigest
      checkerTranscript resourceNoResultMapping solverBuildEvidence
      environmentManifest archiveManifest validatorGate auditTranscript :
      Prop) :
    ay_ecsg_exit_contract benchmarkFingerprint solverCommandManifest
      exitCodeTranscript stdoutStderrDigest labelParseTranscript
      modelProofArtifactDigest checkerTranscript resourceNoResultMapping
      solverBuildEvidence environmentManifest archiveManifest validatorGate
      auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _benchmarkProof _commandProof _exitProof _streamProof _labelProof
          _artifactProof _checkerProof _mappingProof _buildProof
          _environmentProof _archiveProof _gateProof auditProof => auditProof)

theorem ay_ecsg_sat_publication_intro
    (exitContract checkerBackedArtifact checkedModel originalBenchmarkSat :
      Prop) :
    exitContract -> checkerBackedArtifact -> checkedModel ->
    originalBenchmarkSat ->
    ay_ecsg_sat_publication exitContract checkerBackedArtifact checkedModel
      originalBenchmarkSat :=
  fun hcontract hcheckedArtifact hchecked horiginal =>
    ay_ecsg_conj_intro exitContract
      (ay_ecsg_conj checkerBackedArtifact
        (ay_ecsg_conj checkedModel originalBenchmarkSat))
      hcontract
      (ay_ecsg_conj_intro checkerBackedArtifact
        (ay_ecsg_conj checkedModel originalBenchmarkSat)
        hcheckedArtifact
        (ay_ecsg_conj_intro checkedModel originalBenchmarkSat hchecked
          horiginal))

theorem ay_ecsg_unsat_publication_intro
    (exitContract checkerBackedArtifact checkedProof originalBenchmarkUnsat :
      Prop) :
    exitContract -> checkerBackedArtifact -> checkedProof ->
    originalBenchmarkUnsat ->
    ay_ecsg_unsat_publication exitContract checkerBackedArtifact checkedProof
      originalBenchmarkUnsat :=
  fun hcontract hcheckedArtifact hchecked horiginal =>
    ay_ecsg_conj_intro exitContract
      (ay_ecsg_conj checkerBackedArtifact
        (ay_ecsg_conj checkedProof originalBenchmarkUnsat))
      hcontract
      (ay_ecsg_conj_intro checkerBackedArtifact
        (ay_ecsg_conj checkedProof originalBenchmarkUnsat)
        hcheckedArtifact
        (ay_ecsg_conj_intro checkedProof originalBenchmarkUnsat hchecked
          horiginal))

theorem ay_ecsg_sat_requires_checker_backed_artifact
    (exitContract checkerBackedArtifact checkedModel originalBenchmarkSat :
      Prop) :
    ay_ecsg_sat_publication exitContract checkerBackedArtifact checkedModel
      originalBenchmarkSat ->
    checkerBackedArtifact :=
  fun publication =>
    ay_ecsg_conj_left checkerBackedArtifact
      (ay_ecsg_conj checkedModel originalBenchmarkSat)
      (ay_ecsg_conj_right exitContract
        (ay_ecsg_conj checkerBackedArtifact
          (ay_ecsg_conj checkedModel originalBenchmarkSat))
        publication)

theorem ay_ecsg_unsat_requires_checker_backed_artifact
    (exitContract checkerBackedArtifact checkedProof originalBenchmarkUnsat :
      Prop) :
    ay_ecsg_unsat_publication exitContract checkerBackedArtifact checkedProof
      originalBenchmarkUnsat ->
    checkerBackedArtifact :=
  fun publication =>
    ay_ecsg_conj_left checkerBackedArtifact
      (ay_ecsg_conj checkedProof originalBenchmarkUnsat)
      (ay_ecsg_conj_right exitContract
        (ay_ecsg_conj checkerBackedArtifact
          (ay_ecsg_conj checkedProof originalBenchmarkUnsat))
        publication)

theorem ay_ecsg_sat_publication_original_claim
    (exitContract checkerBackedArtifact checkedModel originalBenchmarkSat :
      Prop) :
    ay_ecsg_sat_publication exitContract checkerBackedArtifact checkedModel
      originalBenchmarkSat ->
    originalBenchmarkSat :=
  fun publication =>
    ay_ecsg_conj_right checkedModel originalBenchmarkSat
      (ay_ecsg_conj_right checkerBackedArtifact
        (ay_ecsg_conj checkedModel originalBenchmarkSat)
        (ay_ecsg_conj_right exitContract
          (ay_ecsg_conj checkerBackedArtifact
            (ay_ecsg_conj checkedModel originalBenchmarkSat))
          publication))

theorem ay_ecsg_unsat_publication_original_claim
    (exitContract checkerBackedArtifact checkedProof originalBenchmarkUnsat :
      Prop) :
    ay_ecsg_unsat_publication exitContract checkerBackedArtifact checkedProof
      originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  fun publication =>
    ay_ecsg_conj_right checkedProof originalBenchmarkUnsat
      (ay_ecsg_conj_right checkerBackedArtifact
        (ay_ecsg_conj checkedProof originalBenchmarkUnsat)
        (ay_ecsg_conj_right exitContract
          (ay_ecsg_conj checkerBackedArtifact
            (ay_ecsg_conj checkedProof originalBenchmarkUnsat))
          publication))

theorem ay_ecsg_accepted_exit_preserves_sat_soundness
    (exitContract checkerBackedArtifact checkedModel originalBenchmarkSat :
      Prop) :
    ay_ecsg_sat_publication exitContract checkerBackedArtifact checkedModel
      originalBenchmarkSat ->
    originalBenchmarkSat :=
  ay_ecsg_sat_publication_original_claim exitContract checkerBackedArtifact
    checkedModel originalBenchmarkSat

theorem ay_ecsg_accepted_exit_preserves_unsat_soundness
    (exitContract checkerBackedArtifact checkedProof originalBenchmarkUnsat :
      Prop) :
    ay_ecsg_unsat_publication exitContract checkerBackedArtifact checkedProof
      originalBenchmarkUnsat ->
    originalBenchmarkUnsat :=
  ay_ecsg_unsat_publication_original_claim exitContract checkerBackedArtifact
    checkedProof originalBenchmarkUnsat

theorem ay_ecsg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_ecsg_no_claim reason fallbackPath auditTrail :=
  fun hreason hfallback haudit =>
    ay_ecsg_conj_intro reason (ay_ecsg_conj fallbackPath auditTrail)
      hreason
      (ay_ecsg_conj_intro fallbackPath auditTrail hfallback haudit)

theorem ay_ecsg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_ecsg_blocked_publication satFact unsatFact reason :=
  fun hreason hsat hunsat =>
    ay_ecsg_conj_intro reason
      (ay_ecsg_conj (satFact -> False) (unsatFact -> False))
      hreason
      (ay_ecsg_conj_intro (satFact -> False) (unsatFact -> False)
        hsat hunsat)

theorem ay_ecsg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_ecsg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_ecsg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_ecsg_conj_right reason
        (ay_ecsg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_ecsg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_ecsg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_ecsg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_ecsg_conj_right reason
        (ay_ecsg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_ecsg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_ecsg_recompute reason fallbackPath recomputeObligation :=
  fun hreason hfallback hrecompute =>
    ay_ecsg_conj_intro reason
      (ay_ecsg_conj fallbackPath recomputeObligation)
      hreason
      (ay_ecsg_conj_intro fallbackPath recomputeObligation hfallback
        hrecompute)

theorem ay_ecsg_exit_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecsg_blocked_publication satFact unsatFact reason ->
    ay_ecsg_recompute reason fallbackPath recomputeObligation ->
    ay_ecsg_exit_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun hblocked hrecompute =>
    ay_ecsg_conj_intro
      (ay_ecsg_blocked_publication satFact unsatFact reason)
      (ay_ecsg_recompute reason fallbackPath recomputeObligation)
      hblocked hrecompute

theorem ay_ecsg_exit_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecsg_exit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_ecsg_blocked_publication_no_sat satFact unsatFact reason
      (ay_ecsg_conj_left
        (ay_ecsg_blocked_publication satFact unsatFact reason)
        (ay_ecsg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ecsg_exit_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecsg_exit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_ecsg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_ecsg_conj_left
        (ay_ecsg_blocked_publication satFact unsatFact reason)
        (ay_ecsg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_ecsg_exit_code_alone_cannot_publish_sat
    (satFact unsatFact exitCodeOnly : Prop) :
    ay_ecsg_blocked_publication satFact unsatFact exitCodeOnly ->
    satFact -> False :=
  ay_ecsg_blocked_publication_no_sat satFact unsatFact exitCodeOnly

theorem ay_ecsg_exit_code_alone_cannot_publish_unsat
    (satFact unsatFact exitCodeOnly : Prop) :
    ay_ecsg_blocked_publication satFact unsatFact exitCodeOnly ->
    unsatFact -> False :=
  ay_ecsg_blocked_publication_no_unsat satFact unsatFact exitCodeOnly

theorem ay_ecsg_timeout_exit_forces_no_claim
    (timeoutExit fallbackPath auditTrail : Prop) :
    timeoutExit -> fallbackPath -> auditTrail ->
    ay_ecsg_no_claim timeoutExit fallbackPath auditTrail :=
  ay_ecsg_no_claim_intro timeoutExit fallbackPath auditTrail

theorem ay_ecsg_oom_exit_forces_no_claim
    (oomExit fallbackPath auditTrail : Prop) :
    oomExit -> fallbackPath -> auditTrail ->
    ay_ecsg_no_claim oomExit fallbackPath auditTrail :=
  ay_ecsg_no_claim_intro oomExit fallbackPath auditTrail

theorem ay_ecsg_crash_exit_forces_recompute
    (crashExit fallbackPath recomputeObligation : Prop) :
    crashExit -> fallbackPath -> recomputeObligation ->
    ay_ecsg_recompute crashExit fallbackPath recomputeObligation :=
  ay_ecsg_recompute_intro crashExit fallbackPath recomputeObligation

theorem ay_ecsg_no_result_exit_forces_no_claim
    (noResultExit fallbackPath auditTrail : Prop) :
    noResultExit -> fallbackPath -> auditTrail ->
    ay_ecsg_no_claim noResultExit fallbackPath auditTrail :=
  ay_ecsg_no_claim_intro noResultExit fallbackPath auditTrail

theorem ay_ecsg_mismatch_forces_no_claim
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_ecsg_no_claim reason fallbackPath auditTrail :=
  ay_ecsg_no_claim_intro reason fallbackPath auditTrail

theorem ay_ecsg_exit_mismatch_forces_no_claim
    (exitMismatch fallbackPath auditTrail : Prop) :
    exitMismatch -> fallbackPath -> auditTrail ->
    ay_ecsg_no_claim exitMismatch fallbackPath auditTrail :=
  ay_ecsg_mismatch_forces_no_claim exitMismatch fallbackPath auditTrail

theorem ay_ecsg_stdout_mismatch_forces_no_claim
    (stdoutMismatch fallbackPath auditTrail : Prop) :
    stdoutMismatch -> fallbackPath -> auditTrail ->
    ay_ecsg_no_claim stdoutMismatch fallbackPath auditTrail :=
  ay_ecsg_mismatch_forces_no_claim stdoutMismatch fallbackPath auditTrail

theorem ay_ecsg_artifact_mismatch_forces_no_claim
    (artifactMismatch fallbackPath auditTrail : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    ay_ecsg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_ecsg_mismatch_forces_no_claim artifactMismatch fallbackPath auditTrail

theorem ay_ecsg_checker_mismatch_forces_no_claim
    (checkerMismatch fallbackPath auditTrail : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    ay_ecsg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_ecsg_mismatch_forces_no_claim checkerMismatch fallbackPath auditTrail

theorem ay_ecsg_build_mismatch_forces_no_claim
    (buildMismatch fallbackPath auditTrail : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    ay_ecsg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_ecsg_mismatch_forces_no_claim buildMismatch fallbackPath auditTrail

theorem ay_ecsg_environment_mismatch_forces_no_claim
    (environmentMismatch fallbackPath auditTrail : Prop) :
    environmentMismatch -> fallbackPath -> auditTrail ->
    ay_ecsg_no_claim environmentMismatch fallbackPath auditTrail :=
  ay_ecsg_mismatch_forces_no_claim environmentMismatch fallbackPath auditTrail

theorem ay_ecsg_archive_mismatch_forces_no_claim
    (archiveMismatch fallbackPath auditTrail : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    ay_ecsg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_ecsg_mismatch_forces_no_claim archiveMismatch fallbackPath auditTrail

theorem ay_ecsg_audit_mismatch_forces_recompute
    (auditMismatch fallbackPath recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> recomputeObligation ->
    ay_ecsg_recompute auditMismatch fallbackPath recomputeObligation :=
  ay_ecsg_recompute_intro auditMismatch fallbackPath recomputeObligation

theorem ay_ecsg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecsg_exit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_ecsg_exit_failure_blocks_sat satFact unsatFact reason fallbackPath
    recomputeObligation

theorem ay_ecsg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_ecsg_exit_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_ecsg_exit_failure_blocks_unsat satFact unsatFact reason fallbackPath
    recomputeObligation
