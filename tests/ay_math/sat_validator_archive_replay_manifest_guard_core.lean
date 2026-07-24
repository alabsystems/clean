-- SAT-COMP validator archive replay manifest guard core.
--
-- Public SAT/UNSAT replay from an archive requires immutable benchmark,
-- binary, command, environment, transcript, checker, artifact, resource,
-- fallback, and audit evidence to agree.  Archive replay failures become
-- no-claim recompute obligations rather than public semantic answers.

def ay_armg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_armg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_armg_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_armg_disj satFact (ay_armg_disj unsatFact noClaimFact)

def ay_armg_archive_replay_contract
    (benchmarkArchiveDigest solverBinaryDigest commandLineManifest
      environmentManifest stdoutStderrTranscriptDigest checkerTranscript
      modelProofArtifactDigest resourceLimitManifest noClaimFallback
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkArchiveDigest -> solverBinaryDigest -> commandLineManifest ->
      environmentManifest -> stdoutStderrTranscriptDigest ->
      checkerTranscript -> modelProofArtifactDigest -> resourceLimitManifest ->
      noClaimFallback -> auditTranscript -> result) ->
    result

def ay_armg_sat_publication
    (replayContract acceptedArchiveReplay checkedModel originalModel :
      Prop) : Prop :=
  ay_armg_conj replayContract
    (ay_armg_conj acceptedArchiveReplay
      (ay_armg_conj checkedModel originalModel))

def ay_armg_unsat_publication
    (replayContract acceptedArchiveReplay checkedProof originalEmptyClause :
      Prop) : Prop :=
  ay_armg_conj replayContract
    (ay_armg_conj acceptedArchiveReplay
      (ay_armg_conj checkedProof originalEmptyClause))

def ay_armg_formula_preserved
    (benchmarkArchiveDigest originalBenchmarkFormula replayBenchmarkFormula :
      Prop) : Prop :=
  ay_armg_conj benchmarkArchiveDigest
    (originalBenchmarkFormula -> replayBenchmarkFormula)

def ay_armg_no_claim
    (reason fallbackPath auditTrail : Prop) : Prop :=
  ay_armg_conj reason (ay_armg_conj fallbackPath auditTrail)

def ay_armg_blocked_publication
    (satFact unsatFact reason : Prop) : Prop :=
  ay_armg_conj reason
    (ay_armg_conj (satFact -> False) (unsatFact -> False))

def ay_armg_recompute
    (reason fallbackPath recomputeObligation : Prop) : Prop :=
  ay_armg_conj reason
    (ay_armg_conj fallbackPath recomputeObligation)

def ay_armg_archive_replay_failure
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    Prop :=
  ay_armg_conj
    (ay_armg_blocked_publication satFact unsatFact reason)
    (ay_armg_recompute reason fallbackPath recomputeObligation)

theorem ay_armg_conj_intro (left right : Prop) :
    left -> right -> ay_armg_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_armg_conj_left (left right : Prop) :
    ay_armg_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_armg_conj_right (left right : Prop) :
    ay_armg_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_armg_disj_left (left right : Prop) :
    left -> ay_armg_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_armg_disj_right (left right : Prop) :
    right -> ay_armg_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_armg_archive_replay_contract_intro
    (benchmarkArchiveDigest solverBinaryDigest commandLineManifest
      environmentManifest stdoutStderrTranscriptDigest checkerTranscript
      modelProofArtifactDigest resourceLimitManifest noClaimFallback
      auditTranscript : Prop) :
    benchmarkArchiveDigest -> solverBinaryDigest -> commandLineManifest ->
    environmentManifest -> stdoutStderrTranscriptDigest ->
    checkerTranscript -> modelProofArtifactDigest -> resourceLimitManifest ->
    noClaimFallback -> auditTranscript ->
    ay_armg_archive_replay_contract benchmarkArchiveDigest solverBinaryDigest
      commandLineManifest environmentManifest stdoutStderrTranscriptDigest
      checkerTranscript modelProofArtifactDigest resourceLimitManifest
      noClaimFallback auditTranscript :=
  fun archiveProof binaryProof commandProof environmentProof transcriptProof
      checkerProof artifactProof resourceProof fallbackProof auditProof result
      build =>
    build archiveProof binaryProof commandProof environmentProof
      transcriptProof checkerProof artifactProof resourceProof fallbackProof
      auditProof

theorem ay_armg_contract_archive
    (benchmarkArchiveDigest solverBinaryDigest commandLineManifest
      environmentManifest stdoutStderrTranscriptDigest checkerTranscript
      modelProofArtifactDigest resourceLimitManifest noClaimFallback
      auditTranscript : Prop) :
    ay_armg_archive_replay_contract benchmarkArchiveDigest solverBinaryDigest
      commandLineManifest environmentManifest stdoutStderrTranscriptDigest
      checkerTranscript modelProofArtifactDigest resourceLimitManifest
      noClaimFallback auditTranscript ->
    benchmarkArchiveDigest :=
  fun contract =>
    contract benchmarkArchiveDigest
      (fun archiveProof _binaryProof _commandProof _environmentProof
          _transcriptProof _checkerProof _artifactProof _resourceProof
          _fallbackProof _auditProof => archiveProof)

theorem ay_armg_contract_binary
    (benchmarkArchiveDigest solverBinaryDigest commandLineManifest
      environmentManifest stdoutStderrTranscriptDigest checkerTranscript
      modelProofArtifactDigest resourceLimitManifest noClaimFallback
      auditTranscript : Prop) :
    ay_armg_archive_replay_contract benchmarkArchiveDigest solverBinaryDigest
      commandLineManifest environmentManifest stdoutStderrTranscriptDigest
      checkerTranscript modelProofArtifactDigest resourceLimitManifest
      noClaimFallback auditTranscript ->
    solverBinaryDigest :=
  fun contract =>
    contract solverBinaryDigest
      (fun _archiveProof binaryProof _commandProof _environmentProof
          _transcriptProof _checkerProof _artifactProof _resourceProof
          _fallbackProof _auditProof => binaryProof)

theorem ay_armg_contract_command
    (benchmarkArchiveDigest solverBinaryDigest commandLineManifest
      environmentManifest stdoutStderrTranscriptDigest checkerTranscript
      modelProofArtifactDigest resourceLimitManifest noClaimFallback
      auditTranscript : Prop) :
    ay_armg_archive_replay_contract benchmarkArchiveDigest solverBinaryDigest
      commandLineManifest environmentManifest stdoutStderrTranscriptDigest
      checkerTranscript modelProofArtifactDigest resourceLimitManifest
      noClaimFallback auditTranscript ->
    commandLineManifest :=
  fun contract =>
    contract commandLineManifest
      (fun _archiveProof _binaryProof commandProof _environmentProof
          _transcriptProof _checkerProof _artifactProof _resourceProof
          _fallbackProof _auditProof => commandProof)

theorem ay_armg_contract_environment
    (benchmarkArchiveDigest solverBinaryDigest commandLineManifest
      environmentManifest stdoutStderrTranscriptDigest checkerTranscript
      modelProofArtifactDigest resourceLimitManifest noClaimFallback
      auditTranscript : Prop) :
    ay_armg_archive_replay_contract benchmarkArchiveDigest solverBinaryDigest
      commandLineManifest environmentManifest stdoutStderrTranscriptDigest
      checkerTranscript modelProofArtifactDigest resourceLimitManifest
      noClaimFallback auditTranscript ->
    environmentManifest :=
  fun contract =>
    contract environmentManifest
      (fun _archiveProof _binaryProof _commandProof environmentProof
          _transcriptProof _checkerProof _artifactProof _resourceProof
          _fallbackProof _auditProof => environmentProof)

theorem ay_armg_contract_transcript
    (benchmarkArchiveDigest solverBinaryDigest commandLineManifest
      environmentManifest stdoutStderrTranscriptDigest checkerTranscript
      modelProofArtifactDigest resourceLimitManifest noClaimFallback
      auditTranscript : Prop) :
    ay_armg_archive_replay_contract benchmarkArchiveDigest solverBinaryDigest
      commandLineManifest environmentManifest stdoutStderrTranscriptDigest
      checkerTranscript modelProofArtifactDigest resourceLimitManifest
      noClaimFallback auditTranscript ->
    stdoutStderrTranscriptDigest :=
  fun contract =>
    contract stdoutStderrTranscriptDigest
      (fun _archiveProof _binaryProof _commandProof _environmentProof
          transcriptProof _checkerProof _artifactProof _resourceProof
          _fallbackProof _auditProof => transcriptProof)

theorem ay_armg_contract_checker
    (benchmarkArchiveDigest solverBinaryDigest commandLineManifest
      environmentManifest stdoutStderrTranscriptDigest checkerTranscript
      modelProofArtifactDigest resourceLimitManifest noClaimFallback
      auditTranscript : Prop) :
    ay_armg_archive_replay_contract benchmarkArchiveDigest solverBinaryDigest
      commandLineManifest environmentManifest stdoutStderrTranscriptDigest
      checkerTranscript modelProofArtifactDigest resourceLimitManifest
      noClaimFallback auditTranscript ->
    checkerTranscript :=
  fun contract =>
    contract checkerTranscript
      (fun _archiveProof _binaryProof _commandProof _environmentProof
          _transcriptProof checkerProof _artifactProof _resourceProof
          _fallbackProof _auditProof => checkerProof)

theorem ay_armg_contract_artifact
    (benchmarkArchiveDigest solverBinaryDigest commandLineManifest
      environmentManifest stdoutStderrTranscriptDigest checkerTranscript
      modelProofArtifactDigest resourceLimitManifest noClaimFallback
      auditTranscript : Prop) :
    ay_armg_archive_replay_contract benchmarkArchiveDigest solverBinaryDigest
      commandLineManifest environmentManifest stdoutStderrTranscriptDigest
      checkerTranscript modelProofArtifactDigest resourceLimitManifest
      noClaimFallback auditTranscript ->
    modelProofArtifactDigest :=
  fun contract =>
    contract modelProofArtifactDigest
      (fun _archiveProof _binaryProof _commandProof _environmentProof
          _transcriptProof _checkerProof artifactProof _resourceProof
          _fallbackProof _auditProof => artifactProof)

theorem ay_armg_contract_resource
    (benchmarkArchiveDigest solverBinaryDigest commandLineManifest
      environmentManifest stdoutStderrTranscriptDigest checkerTranscript
      modelProofArtifactDigest resourceLimitManifest noClaimFallback
      auditTranscript : Prop) :
    ay_armg_archive_replay_contract benchmarkArchiveDigest solverBinaryDigest
      commandLineManifest environmentManifest stdoutStderrTranscriptDigest
      checkerTranscript modelProofArtifactDigest resourceLimitManifest
      noClaimFallback auditTranscript ->
    resourceLimitManifest :=
  fun contract =>
    contract resourceLimitManifest
      (fun _archiveProof _binaryProof _commandProof _environmentProof
          _transcriptProof _checkerProof _artifactProof resourceProof
          _fallbackProof _auditProof => resourceProof)

theorem ay_armg_contract_fallback
    (benchmarkArchiveDigest solverBinaryDigest commandLineManifest
      environmentManifest stdoutStderrTranscriptDigest checkerTranscript
      modelProofArtifactDigest resourceLimitManifest noClaimFallback
      auditTranscript : Prop) :
    ay_armg_archive_replay_contract benchmarkArchiveDigest solverBinaryDigest
      commandLineManifest environmentManifest stdoutStderrTranscriptDigest
      checkerTranscript modelProofArtifactDigest resourceLimitManifest
      noClaimFallback auditTranscript ->
    noClaimFallback :=
  fun contract =>
    contract noClaimFallback
      (fun _archiveProof _binaryProof _commandProof _environmentProof
          _transcriptProof _checkerProof _artifactProof _resourceProof
          fallbackProof _auditProof => fallbackProof)

theorem ay_armg_contract_audit
    (benchmarkArchiveDigest solverBinaryDigest commandLineManifest
      environmentManifest stdoutStderrTranscriptDigest checkerTranscript
      modelProofArtifactDigest resourceLimitManifest noClaimFallback
      auditTranscript : Prop) :
    ay_armg_archive_replay_contract benchmarkArchiveDigest solverBinaryDigest
      commandLineManifest environmentManifest stdoutStderrTranscriptDigest
      checkerTranscript modelProofArtifactDigest resourceLimitManifest
      noClaimFallback auditTranscript ->
    auditTranscript :=
  fun contract =>
    contract auditTranscript
      (fun _archiveProof _binaryProof _commandProof _environmentProof
          _transcriptProof _checkerProof _artifactProof _resourceProof
          _fallbackProof auditProof => auditProof)

theorem ay_armg_sat_publication_intro
    (replayContract acceptedArchiveReplay checkedModel originalModel :
      Prop) :
    replayContract -> acceptedArchiveReplay -> checkedModel ->
    originalModel ->
    ay_armg_sat_publication replayContract acceptedArchiveReplay
      checkedModel originalModel :=
  fun contractProof acceptedProof modelProof originalProof =>
    ay_armg_conj_intro replayContract
      (ay_armg_conj acceptedArchiveReplay
        (ay_armg_conj checkedModel originalModel))
      contractProof
      (ay_armg_conj_intro acceptedArchiveReplay
        (ay_armg_conj checkedModel originalModel)
        acceptedProof
        (ay_armg_conj_intro checkedModel originalModel modelProof
          originalProof))

theorem ay_armg_sat_publication_replay
    (replayContract acceptedArchiveReplay checkedModel originalModel :
      Prop) :
    ay_armg_sat_publication replayContract acceptedArchiveReplay
      checkedModel originalModel ->
    replayContract :=
  fun publication =>
    ay_armg_conj_left replayContract
      (ay_armg_conj acceptedArchiveReplay
        (ay_armg_conj checkedModel originalModel))
      publication

theorem ay_armg_sat_publication_original_model
    (replayContract acceptedArchiveReplay checkedModel originalModel :
      Prop) :
    ay_armg_sat_publication replayContract acceptedArchiveReplay
      checkedModel originalModel ->
    originalModel :=
  fun publication =>
    ay_armg_conj_right checkedModel originalModel
      (ay_armg_conj_right acceptedArchiveReplay
        (ay_armg_conj checkedModel originalModel)
        (ay_armg_conj_right replayContract
          (ay_armg_conj acceptedArchiveReplay
            (ay_armg_conj checkedModel originalModel))
          publication))

theorem ay_armg_unsat_publication_intro
    (replayContract acceptedArchiveReplay checkedProof originalEmptyClause :
      Prop) :
    replayContract -> acceptedArchiveReplay -> checkedProof ->
    originalEmptyClause ->
    ay_armg_unsat_publication replayContract acceptedArchiveReplay
      checkedProof originalEmptyClause :=
  fun contractProof acceptedProof proofProof originalProof =>
    ay_armg_conj_intro replayContract
      (ay_armg_conj acceptedArchiveReplay
        (ay_armg_conj checkedProof originalEmptyClause))
      contractProof
      (ay_armg_conj_intro acceptedArchiveReplay
        (ay_armg_conj checkedProof originalEmptyClause)
        acceptedProof
        (ay_armg_conj_intro checkedProof originalEmptyClause proofProof
          originalProof))

theorem ay_armg_unsat_publication_replay
    (replayContract acceptedArchiveReplay checkedProof originalEmptyClause :
      Prop) :
    ay_armg_unsat_publication replayContract acceptedArchiveReplay
      checkedProof originalEmptyClause ->
    replayContract :=
  fun publication =>
    ay_armg_conj_left replayContract
      (ay_armg_conj acceptedArchiveReplay
        (ay_armg_conj checkedProof originalEmptyClause))
      publication

theorem ay_armg_unsat_publication_original_empty_clause
    (replayContract acceptedArchiveReplay checkedProof originalEmptyClause :
      Prop) :
    ay_armg_unsat_publication replayContract acceptedArchiveReplay
      checkedProof originalEmptyClause ->
    originalEmptyClause :=
  fun publication =>
    ay_armg_conj_right checkedProof originalEmptyClause
      (ay_armg_conj_right acceptedArchiveReplay
        (ay_armg_conj checkedProof originalEmptyClause)
        (ay_armg_conj_right replayContract
          (ay_armg_conj acceptedArchiveReplay
            (ay_armg_conj checkedProof originalEmptyClause))
          publication))

theorem ay_armg_accepted_replay_sat_passes_publication
    (replayContract acceptedArchiveReplay checkedModel originalModel :
      Prop) :
    ay_armg_sat_publication replayContract acceptedArchiveReplay
      checkedModel originalModel ->
    ay_armg_public_result originalModel False False :=
  fun publication =>
    ay_armg_disj_left originalModel (ay_armg_disj False False)
      (ay_armg_sat_publication_original_model replayContract
        acceptedArchiveReplay checkedModel originalModel publication)

theorem ay_armg_accepted_replay_unsat_passes_publication
    (replayContract acceptedArchiveReplay checkedProof originalEmptyClause :
      Prop) :
    ay_armg_unsat_publication replayContract acceptedArchiveReplay
      checkedProof originalEmptyClause ->
    ay_armg_public_result False originalEmptyClause False :=
  fun publication =>
    ay_armg_disj_right False (ay_armg_disj originalEmptyClause False)
      (ay_armg_disj_left originalEmptyClause False
        (ay_armg_unsat_publication_original_empty_clause replayContract
          acceptedArchiveReplay checkedProof originalEmptyClause publication))

theorem ay_armg_formula_preserved_intro
    (benchmarkArchiveDigest originalBenchmarkFormula replayBenchmarkFormula :
      Prop) :
    benchmarkArchiveDigest ->
    (originalBenchmarkFormula -> replayBenchmarkFormula) ->
    ay_armg_formula_preserved benchmarkArchiveDigest originalBenchmarkFormula
      replayBenchmarkFormula :=
  fun archiveProof preserved =>
    ay_armg_conj_intro benchmarkArchiveDigest
      (originalBenchmarkFormula -> replayBenchmarkFormula)
      archiveProof preserved

theorem ay_armg_replay_never_changes_original_benchmark_formula
    (benchmarkArchiveDigest originalBenchmarkFormula replayBenchmarkFormula :
      Prop) :
    ay_armg_formula_preserved benchmarkArchiveDigest originalBenchmarkFormula
      replayBenchmarkFormula ->
    originalBenchmarkFormula -> replayBenchmarkFormula :=
  fun preserved =>
    ay_armg_conj_right benchmarkArchiveDigest
      (originalBenchmarkFormula -> replayBenchmarkFormula)
      preserved

theorem ay_armg_no_claim_intro
    (reason fallbackPath auditTrail : Prop) :
    reason -> fallbackPath -> auditTrail ->
    ay_armg_no_claim reason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof =>
    ay_armg_conj_intro reason (ay_armg_conj fallbackPath auditTrail)
      reasonProof
      (ay_armg_conj_intro fallbackPath auditTrail fallbackProof auditProof)

theorem ay_armg_blocked_publication_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_armg_blocked_publication satFact unsatFact reason :=
  fun reasonProof noSat noUnsat =>
    ay_armg_conj_intro reason
      (ay_armg_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_armg_conj_intro (satFact -> False) (unsatFact -> False)
        noSat noUnsat)

theorem ay_armg_blocked_publication_no_sat
    (satFact unsatFact reason : Prop) :
    ay_armg_blocked_publication satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_armg_conj_left (satFact -> False) (unsatFact -> False)
      (ay_armg_conj_right reason
        (ay_armg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_armg_blocked_publication_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_armg_blocked_publication satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_armg_conj_right (satFact -> False) (unsatFact -> False)
      (ay_armg_conj_right reason
        (ay_armg_conj (satFact -> False) (unsatFact -> False))
        blocked)

theorem ay_armg_recompute_intro
    (reason fallbackPath recomputeObligation : Prop) :
    reason -> fallbackPath -> recomputeObligation ->
    ay_armg_recompute reason fallbackPath recomputeObligation :=
  fun reasonProof fallbackProof recomputeProof =>
    ay_armg_conj_intro reason
      (ay_armg_conj fallbackPath recomputeObligation)
      reasonProof
      (ay_armg_conj_intro fallbackPath recomputeObligation fallbackProof
        recomputeProof)

theorem ay_armg_archive_replay_failure_intro
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_armg_blocked_publication satFact unsatFact reason ->
    ay_armg_recompute reason fallbackPath recomputeObligation ->
    ay_armg_archive_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation :=
  fun blocked recompute =>
    ay_armg_conj_intro
      (ay_armg_blocked_publication satFact unsatFact reason)
      (ay_armg_recompute reason fallbackPath recomputeObligation)
      blocked recompute

theorem ay_armg_archive_replay_failure_blocks_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_armg_archive_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  fun failure =>
    ay_armg_blocked_publication_no_sat satFact unsatFact reason
      (ay_armg_conj_left
        (ay_armg_blocked_publication satFact unsatFact reason)
        (ay_armg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_armg_archive_replay_failure_blocks_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_armg_archive_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  fun failure =>
    ay_armg_blocked_publication_no_unsat satFact unsatFact reason
      (ay_armg_conj_left
        (ay_armg_blocked_publication satFact unsatFact reason)
        (ay_armg_recompute reason fallbackPath recomputeObligation)
        failure)

theorem ay_armg_archive_replay_failure_recompute
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_armg_archive_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    ay_armg_recompute reason fallbackPath recomputeObligation :=
  fun failure =>
    ay_armg_conj_right
      (ay_armg_blocked_publication satFact unsatFact reason)
      (ay_armg_recompute reason fallbackPath recomputeObligation)
      failure

theorem ay_armg_mismatch_forces_no_claim
    (satFact unsatFact mismatchReason fallbackPath auditTrail
      recomputeObligation : Prop) :
    mismatchReason -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_armg_no_claim mismatchReason fallbackPath auditTrail :=
  fun reasonProof fallbackProof auditProof _noSat _noUnsat
      _recomputeProof =>
    ay_armg_no_claim_intro mismatchReason fallbackPath auditTrail
      reasonProof fallbackProof auditProof

theorem ay_armg_archive_mismatch_forces_no_claim
    (satFact unsatFact archiveMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    archiveMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_armg_no_claim archiveMismatch fallbackPath auditTrail :=
  ay_armg_mismatch_forces_no_claim satFact unsatFact archiveMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_armg_binary_mismatch_forces_no_claim
    (satFact unsatFact binaryMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    binaryMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_armg_no_claim binaryMismatch fallbackPath auditTrail :=
  ay_armg_mismatch_forces_no_claim satFact unsatFact binaryMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_armg_command_mismatch_forces_no_claim
    (satFact unsatFact commandMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    commandMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_armg_no_claim commandMismatch fallbackPath auditTrail :=
  ay_armg_mismatch_forces_no_claim satFact unsatFact commandMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_armg_environment_mismatch_forces_no_claim
    (satFact unsatFact environmentMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    environmentMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_armg_no_claim environmentMismatch fallbackPath auditTrail :=
  ay_armg_mismatch_forces_no_claim satFact unsatFact environmentMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_armg_transcript_mismatch_forces_no_claim
    (satFact unsatFact transcriptMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    transcriptMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_armg_no_claim transcriptMismatch fallbackPath auditTrail :=
  ay_armg_mismatch_forces_no_claim satFact unsatFact transcriptMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_armg_checker_mismatch_forces_no_claim
    (satFact unsatFact checkerMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    checkerMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_armg_no_claim checkerMismatch fallbackPath auditTrail :=
  ay_armg_mismatch_forces_no_claim satFact unsatFact checkerMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_armg_artifact_mismatch_forces_no_claim
    (satFact unsatFact artifactMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    artifactMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_armg_no_claim artifactMismatch fallbackPath auditTrail :=
  ay_armg_mismatch_forces_no_claim satFact unsatFact artifactMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_armg_resource_mismatch_forces_no_claim
    (satFact unsatFact resourceMismatch fallbackPath auditTrail
      recomputeObligation : Prop) :
    resourceMismatch -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_armg_no_claim resourceMismatch fallbackPath auditTrail :=
  ay_armg_mismatch_forces_no_claim satFact unsatFact resourceMismatch
    fallbackPath auditTrail recomputeObligation

theorem ay_armg_fallback_activation_forces_no_claim
    (satFact unsatFact fallbackActivation fallbackPath auditTrail
      recomputeObligation : Prop) :
    fallbackActivation -> fallbackPath -> auditTrail ->
    (satFact -> False) -> (unsatFact -> False) -> recomputeObligation ->
    ay_armg_no_claim fallbackActivation fallbackPath auditTrail :=
  ay_armg_mismatch_forces_no_claim satFact unsatFact fallbackActivation
    fallbackPath auditTrail recomputeObligation

theorem ay_armg_audit_mismatch_forces_recompute
    (satFact unsatFact auditMismatch fallbackPath recomputeObligation :
      Prop) :
    auditMismatch -> (satFact -> False) -> (unsatFact -> False) ->
    fallbackPath -> recomputeObligation ->
    ay_armg_archive_replay_failure satFact unsatFact auditMismatch
      fallbackPath recomputeObligation :=
  fun reasonProof noSat noUnsat fallbackProof recomputeProof =>
    ay_armg_archive_replay_failure_intro satFact unsatFact auditMismatch
      fallbackPath recomputeObligation
      (ay_armg_blocked_publication_intro satFact unsatFact auditMismatch
        reasonProof noSat noUnsat)
      (ay_armg_recompute_intro auditMismatch fallbackPath recomputeObligation
        reasonProof fallbackProof recomputeProof)

theorem ay_armg_failed_archive_replay_cannot_bless_sat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_armg_archive_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    satFact -> False :=
  ay_armg_archive_replay_failure_blocks_sat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_armg_failed_archive_replay_cannot_bless_unsat
    (satFact unsatFact reason fallbackPath recomputeObligation : Prop) :
    ay_armg_archive_replay_failure satFact unsatFact reason fallbackPath
      recomputeObligation ->
    unsatFact -> False :=
  ay_armg_archive_replay_failure_blocks_unsat satFact unsatFact reason
    fallbackPath recomputeObligation

theorem ay_armg_no_claim_cannot_create_public_sat
    (satFact reason fallbackPath auditTrail : Prop) :
    ay_armg_no_claim reason fallbackPath auditTrail ->
    (reason -> satFact -> False) -> satFact -> False :=
  fun noClaim reasonBlocksSat satProof =>
    reasonBlocksSat
      (ay_armg_conj_left reason (ay_armg_conj fallbackPath auditTrail)
        noClaim)
      satProof

theorem ay_armg_no_claim_cannot_create_public_unsat
    (unsatFact reason fallbackPath auditTrail : Prop) :
    ay_armg_no_claim reason fallbackPath auditTrail ->
    (reason -> unsatFact -> False) -> unsatFact -> False :=
  fun noClaim reasonBlocksUnsat unsatProof =>
    reasonBlocksUnsat
      (ay_armg_conj_left reason (ay_armg_conj fallbackPath auditTrail)
        noClaim)
      unsatProof
