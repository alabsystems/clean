-- SAT-COMP validator sequential-main parallel-noise rejection guard core.
--
-- Public SAT/UNSAT claims for sequential main require single-process evidence,
-- CPU-affinity evidence, no helper-solver evidence, deterministic seed
-- manifest, transcripts, checker output, benchmark fingerprint, build evidence,
-- archive evidence, fallback, and audit transcript to agree.

def ay_pnrg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_pnrg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_pnrg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_pnrg_disj satFact (ay_pnrg_disj unsatFact noClaimFact)

def ay_pnrg_sequential_main_contract
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (singleProcessRunManifest -> cpuAffinityEvidence ->
      noHelperSolverEvidence -> deterministicRandomSeedManifest ->
      stdoutStderrTranscriptDigest -> checkerTranscript ->
      benchmarkFingerprint -> solverBuildEvidence -> archiveManifest ->
      fallbackNoClaimPath -> auditTranscript -> result) ->
    result

def ay_pnrg_sat_publication
    (noiseContract acceptedSequentialMain checkedModel originalModel :
      Prop) : Prop :=
  ay_pnrg_conj noiseContract
    (ay_pnrg_conj acceptedSequentialMain
      (ay_pnrg_conj checkedModel originalModel))

def ay_pnrg_unsat_publication
    (noiseContract acceptedSequentialMain checkedProof originalEmptyClause :
      Prop) : Prop :=
  ay_pnrg_conj noiseContract
    (ay_pnrg_conj acceptedSequentialMain
      (ay_pnrg_conj checkedProof originalEmptyClause))

def ay_pnrg_semantics_preserved
    (originalBenchmarkFormula replayBenchmarkFormula : Prop) : Prop :=
  originalBenchmarkFormula -> replayBenchmarkFormula

def ay_pnrg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_pnrg_conj reason (ay_pnrg_conj fallbackPath auditTrail)

def ay_pnrg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_pnrg_conj reason
    (ay_pnrg_conj (satFact -> False) (unsatFact -> False))

def ay_pnrg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_pnrg_conj reason
    (ay_pnrg_conj fallbackPath recomputeObligation)

def ay_pnrg_parallel_noise_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_pnrg_conj
    (ay_pnrg_blocked_publication satFact unsatFact reason)
    (ay_pnrg_recompute reason fallbackPath recomputeObligation)

theorem ay_pnrg_conj_intro (left right : Prop) :
    left -> right -> ay_pnrg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_pnrg_conj_left (left right : Prop) :
    ay_pnrg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_pnrg_conj_right (left right : Prop) :
    ay_pnrg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_pnrg_disj_left (left right : Prop) :
    left -> ay_pnrg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_pnrg_disj_right (left right : Prop) :
    right -> ay_pnrg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_pnrg_sequential_main_contract_intro
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    singleProcessRunManifest -> cpuAffinityEvidence ->
    noHelperSolverEvidence -> deterministicRandomSeedManifest ->
    stdoutStderrTranscriptDigest -> checkerTranscript ->
    benchmarkFingerprint -> solverBuildEvidence -> archiveManifest ->
    fallbackNoClaimPath -> auditTranscript ->
    ay_pnrg_sequential_main_contract singleProcessRunManifest
      cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript :=
  fun processProof affinityProof helperProof seedProof transcriptProof
      checkerProof fingerprintProof buildProof archiveProof fallbackProof
      auditProof result build =>
    build processProof affinityProof helperProof seedProof transcriptProof
      checkerProof fingerprintProof buildProof archiveProof fallbackProof
      auditProof

theorem ay_pnrg_contract_process
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_pnrg_sequential_main_contract singleProcessRunManifest
      cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    singleProcessRunManifest :=
  fun contract =>
    contract singleProcessRunManifest
      (fun processProof _affinityProof _helperProof _seedProof
          _transcriptProof _checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => processProof)

theorem ay_pnrg_contract_affinity
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_pnrg_sequential_main_contract singleProcessRunManifest
      cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    cpuAffinityEvidence :=
  fun contract =>
    contract cpuAffinityEvidence
      (fun _processProof affinityProof _helperProof _seedProof
          _transcriptProof _checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => affinityProof)

theorem ay_pnrg_contract_no_helper
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_pnrg_sequential_main_contract singleProcessRunManifest
      cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    noHelperSolverEvidence :=
  fun contract =>
    contract noHelperSolverEvidence
      (fun _processProof _affinityProof helperProof _seedProof
          _transcriptProof _checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => helperProof)

theorem ay_pnrg_contract_seed
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_pnrg_sequential_main_contract singleProcessRunManifest
      cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    deterministicRandomSeedManifest :=
  fun contract =>
    contract deterministicRandomSeedManifest
      (fun _processProof _affinityProof _helperProof seedProof
          _transcriptProof _checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => seedProof)

theorem ay_pnrg_contract_transcript
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_pnrg_sequential_main_contract singleProcessRunManifest
      cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    stdoutStderrTranscriptDigest :=
  fun contract =>
    contract stdoutStderrTranscriptDigest
      (fun _processProof _affinityProof _helperProof _seedProof
          transcriptProof _checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => transcriptProof)

theorem ay_pnrg_contract_checker
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_pnrg_sequential_main_contract singleProcessRunManifest
      cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _processProof _affinityProof _helperProof _seedProof
          _transcriptProof checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => checkerProof)

theorem ay_pnrg_contract_fingerprint
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_pnrg_sequential_main_contract singleProcessRunManifest
      cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    benchmarkFingerprint :=
  fun contract =>
    contract benchmarkFingerprint
      (fun _processProof _affinityProof _helperProof _seedProof
          _transcriptProof _checkerProof fingerprintProof _buildProof
          _archiveProof _fallbackProof _auditProof => fingerprintProof)

theorem ay_pnrg_contract_build
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_pnrg_sequential_main_contract singleProcessRunManifest
      cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun contract =>
    contract solverBuildEvidence
      (fun _processProof _affinityProof _helperProof _seedProof
          _transcriptProof _checkerProof _fingerprintProof buildProof
          _archiveProof _fallbackProof _auditProof => buildProof)

theorem ay_pnrg_contract_archive
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_pnrg_sequential_main_contract singleProcessRunManifest
      cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun contract =>
    contract archiveManifest
      (fun _processProof _affinityProof _helperProof _seedProof
          _transcriptProof _checkerProof _fingerprintProof _buildProof
          archiveProof _fallbackProof _auditProof => archiveProof)

theorem ay_pnrg_contract_fallback
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_pnrg_sequential_main_contract singleProcessRunManifest
      cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun contract =>
    contract fallbackNoClaimPath
      (fun _processProof _affinityProof _helperProof _seedProof
          _transcriptProof _checkerProof _fingerprintProof _buildProof
          _archiveProof fallbackProof _auditProof => fallbackProof)

theorem ay_pnrg_contract_audit
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_pnrg_sequential_main_contract singleProcessRunManifest
      cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _processProof _affinityProof _helperProof _seedProof
          _transcriptProof _checkerProof _fingerprintProof _buildProof
          _archiveProof _fallbackProof auditProof => auditProof)

theorem ay_pnrg_sat_publication_intro
    (noiseContract acceptedSequentialMain checkedModel originalModel :
      Prop) :
    noiseContract -> acceptedSequentialMain -> checkedModel -> originalModel ->
    ay_pnrg_sat_publication noiseContract acceptedSequentialMain checkedModel
      originalModel :=
  fun contractProof acceptedProof modelProof originalProof =>
    ay_pnrg_conj_intro noiseContract
      (ay_pnrg_conj acceptedSequentialMain
        (ay_pnrg_conj checkedModel originalModel))
      contractProof
      (ay_pnrg_conj_intro acceptedSequentialMain
        (ay_pnrg_conj checkedModel originalModel)
        acceptedProof
        (ay_pnrg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_pnrg_unsat_publication_intro
    (noiseContract acceptedSequentialMain checkedProof originalEmptyClause :
      Prop) :
    noiseContract -> acceptedSequentialMain -> checkedProof ->
    originalEmptyClause ->
    ay_pnrg_unsat_publication noiseContract acceptedSequentialMain
      checkedProof originalEmptyClause :=
  fun contractProof acceptedProof proofProof originalProof =>
    ay_pnrg_conj_intro noiseContract
      (ay_pnrg_conj acceptedSequentialMain
        (ay_pnrg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_pnrg_conj_intro acceptedSequentialMain
        (ay_pnrg_conj checkedProof originalEmptyClause)
        acceptedProof
        (ay_pnrg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_pnrg_sat_publication_original_model
    (noiseContract acceptedSequentialMain checkedModel originalModel :
      Prop) :
    ay_pnrg_sat_publication noiseContract acceptedSequentialMain checkedModel
      originalModel ->
    originalModel :=
  fun publication =>
    ay_pnrg_conj_right checkedModel originalModel
      (ay_pnrg_conj_right acceptedSequentialMain
        (ay_pnrg_conj checkedModel originalModel)
        (ay_pnrg_conj_right noiseContract
          (ay_pnrg_conj acceptedSequentialMain
            (ay_pnrg_conj checkedModel originalModel))
          publication))

theorem ay_pnrg_unsat_publication_original_empty_clause
    (noiseContract acceptedSequentialMain checkedProof originalEmptyClause :
      Prop) :
    ay_pnrg_unsat_publication noiseContract acceptedSequentialMain
      checkedProof originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_pnrg_conj_right checkedProof originalEmptyClause
      (ay_pnrg_conj_right acceptedSequentialMain
        (ay_pnrg_conj checkedProof originalEmptyClause)
        (ay_pnrg_conj_right noiseContract
          (ay_pnrg_conj acceptedSequentialMain
            (ay_pnrg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_pnrg_accepted_evidence_confirms_sequential_main
    (singleProcessRunManifest cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_pnrg_sequential_main_contract singleProcessRunManifest
      cpuAffinityEvidence noHelperSolverEvidence
      deterministicRandomSeedManifest stdoutStderrTranscriptDigest
      checkerTranscript benchmarkFingerprint solverBuildEvidence
      archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_pnrg_conj singleProcessRunManifest
      (ay_pnrg_conj cpuAffinityEvidence noHelperSolverEvidence) :=
  fun contract =>
    ay_pnrg_conj_intro singleProcessRunManifest
      (ay_pnrg_conj cpuAffinityEvidence noHelperSolverEvidence)
      (ay_pnrg_contract_process singleProcessRunManifest cpuAffinityEvidence
        noHelperSolverEvidence deterministicRandomSeedManifest
        stdoutStderrTranscriptDigest checkerTranscript benchmarkFingerprint
        solverBuildEvidence archiveManifest fallbackNoClaimPath auditTranscript
        contract)
      (ay_pnrg_conj_intro cpuAffinityEvidence noHelperSolverEvidence
        (ay_pnrg_contract_affinity singleProcessRunManifest
          cpuAffinityEvidence noHelperSolverEvidence
          deterministicRandomSeedManifest stdoutStderrTranscriptDigest
          checkerTranscript benchmarkFingerprint solverBuildEvidence
          archiveManifest fallbackNoClaimPath auditTranscript contract)
        (ay_pnrg_contract_no_helper singleProcessRunManifest
          cpuAffinityEvidence noHelperSolverEvidence
          deterministicRandomSeedManifest stdoutStderrTranscriptDigest
          checkerTranscript benchmarkFingerprint solverBuildEvidence
          archiveManifest fallbackNoClaimPath auditTranscript contract))

theorem ay_pnrg_accepted_sequential_sat_passes_publication
    (noiseContract acceptedSequentialMain checkedModel originalModel : Prop) :
    ay_pnrg_sat_publication noiseContract acceptedSequentialMain
      checkedModel originalModel ->
    ay_pnrg_public_result originalModel False False :=
  fun publication =>
    ay_pnrg_disj_left originalModel (ay_pnrg_disj False False)
      (ay_pnrg_sat_publication_original_model noiseContract
        acceptedSequentialMain checkedModel originalModel publication)

theorem ay_pnrg_accepted_sequential_unsat_passes_publication
    (noiseContract acceptedSequentialMain checkedProof originalEmptyClause :
      Prop) :
    ay_pnrg_unsat_publication noiseContract acceptedSequentialMain
      checkedProof originalEmptyClause ->
    ay_pnrg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_pnrg_disj_right False (ay_pnrg_disj originalEmptyClause False)
      (ay_pnrg_disj_left originalEmptyClause False
        (ay_pnrg_unsat_publication_original_empty_clause noiseContract
          acceptedSequentialMain checkedProof originalEmptyClause publication))

theorem ay_pnrg_does_not_change_original_benchmark_semantics
    (originalBenchmarkFormula replayBenchmarkFormula : Prop) :
    ay_pnrg_semantics_preserved originalBenchmarkFormula
      replayBenchmarkFormula ->
    originalBenchmarkFormula -> replayBenchmarkFormula :=
  fun preserved => preserved

theorem ay_pnrg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_pnrg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_pnrg_conj_intro reason (ay_pnrg_conj fallbackPath auditTrail)
      reasonProof
      (ay_pnrg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_pnrg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_pnrg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_pnrg_conj_intro reason
      (ay_pnrg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_pnrg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_pnrg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_pnrg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_pnrg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_pnrg_conj_right reason
        (ay_pnrg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_pnrg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_pnrg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_pnrg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_pnrg_conj_right reason
        (ay_pnrg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_pnrg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_pnrg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_pnrg_conj_intro reason
      (ay_pnrg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_pnrg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_pnrg_parallel_noise_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_pnrg_blocked_publication satFact unsatFact reason ->
    ay_pnrg_recompute reason fallbackPath recomputeObligation ->
    ay_pnrg_parallel_noise_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_pnrg_conj_intro
      (ay_pnrg_blocked_publication satFact unsatFact reason)
      (ay_pnrg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_pnrg_parallel_noise_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_pnrg_parallel_noise_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_pnrg_blocked_publication_no_sat satFact unsatFact reason
      (ay_pnrg_conj_left
        (ay_pnrg_blocked_publication satFact unsatFact reason)
        (ay_pnrg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_pnrg_parallel_noise_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_pnrg_parallel_noise_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_pnrg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_pnrg_conj_left
        (ay_pnrg_blocked_publication satFact unsatFact reason)
        (ay_pnrg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_pnrg_parallel_noise_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_pnrg_parallel_noise_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_pnrg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_pnrg_conj_right
      (ay_pnrg_blocked_publication satFact unsatFact reason)
      (ay_pnrg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_pnrg_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_pnrg_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_pnrg_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_pnrg_process_mismatch_forces_no_claim
    (satFact unsatFact processMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    processMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_pnrg_no_claim processMismatch fallbackPath auditTrail :=
  ay_pnrg_mismatch_forces_no_claim satFact unsatFact processMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_pnrg_affinity_mismatch_forces_no_claim
    (satFact unsatFact affinityMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    affinityMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_pnrg_no_claim affinityMismatch fallbackPath auditTrail :=
  ay_pnrg_mismatch_forces_no_claim satFact unsatFact affinityMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_pnrg_helper_mismatch_forces_no_claim
    (satFact unsatFact helperMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    helperMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_pnrg_no_claim helperMismatch fallbackPath auditTrail :=
  ay_pnrg_mismatch_forces_no_claim satFact unsatFact helperMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_pnrg_seed_mismatch_forces_no_claim
    (satFact unsatFact seedMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    seedMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_pnrg_no_claim seedMismatch fallbackPath auditTrail :=
  ay_pnrg_mismatch_forces_no_claim satFact unsatFact seedMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_pnrg_transcript_mismatch_forces_no_claim
    (satFact unsatFact transcriptMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    transcriptMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_pnrg_no_claim transcriptMismatch fallbackPath auditTrail :=
  ay_pnrg_mismatch_forces_no_claim satFact unsatFact transcriptMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_pnrg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_pnrg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_pnrg_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_pnrg_fingerprint_mismatch_forces_no_claim
    (satFact unsatFact fingerprintMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    fingerprintMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_pnrg_no_claim fingerprintMismatch fallbackPath auditTrail :=
  ay_pnrg_mismatch_forces_no_claim satFact unsatFact fingerprintMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_pnrg_build_mismatch_forces_no_claim
    (satFact unsatFact buildMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    buildMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_pnrg_no_claim buildMismatch fallbackPath auditTrail :=
  ay_pnrg_mismatch_forces_no_claim satFact unsatFact buildMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_pnrg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_pnrg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_pnrg_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_pnrg_audit_mismatch_forces_no_claim
    (satFact unsatFact auditMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    auditMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_pnrg_no_claim auditMismatch fallbackPath auditTrail :=
  ay_pnrg_mismatch_forces_no_claim satFact unsatFact auditMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_pnrg_fallback_activation_forces_recompute
    (satFact unsatFact fallbackActivation fallbackPath recomputeObligation :
      Prop) :
    fallbackActivation -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_pnrg_parallel_noise_failure satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_pnrg_parallel_noise_failure_intro satFact unsatFact fallbackActivation
      fallbackPath recomputeObligation
      (ay_pnrg_blocked_publication_intro satFact unsatFact fallbackActivation
        reasonProof noSat noUnsat)
      (ay_pnrg_recompute_intro fallbackActivation fallbackPath
        recomputeObligation reasonProof fallbackProof recomputeProof)

theorem ay_pnrg_failed_guard_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_pnrg_parallel_noise_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_pnrg_parallel_noise_failure_blocks_sat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_pnrg_failed_guard_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_pnrg_parallel_noise_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_pnrg_parallel_noise_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_pnrg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_pnrg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_pnrg_conj_left reason (ay_pnrg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_pnrg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_pnrg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_pnrg_conj_left reason (ay_pnrg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
