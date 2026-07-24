-- Archive replay-script guard for sequential-main SAT-COMP validation.
-- Self-contained propositional contract for replayable ay result artifacts.

def ay_arpg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_arpg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

theorem ay_arpg_conj_intro {left right : Prop} (hleft : left) (hright : right) :
    ay_arpg_conj left right :=
  fun result k => k hleft hright

theorem ay_arpg_conj_left {left right : Prop} (h : ay_arpg_conj left right) :
    left :=
  h left (fun hleft _ => hleft)

theorem ay_arpg_conj_right {left right : Prop} (h : ay_arpg_conj left right) :
    right :=
  h right (fun _ hright => hright)

theorem ay_arpg_disj_left {left right : Prop} (hleft : left) :
    ay_arpg_disj left right :=
  fun result kleft _ => kleft hleft

theorem ay_arpg_disj_right {left right : Prop} (hright : right) :
    ay_arpg_disj left right :=
  fun result _ kright => kright hright

def ay_arpg_replay_contract
    (benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkFingerprint ->
      archiveManifestDigest ->
      replayScriptDigest ->
      solverBinaryBuildDigest ->
      checkerBinaryVersionDigest ->
      environmentManifest ->
      commandLineManifest ->
      expectedOutputDigest ->
      modelProofArtifactDigest ->
      checkerTranscript ->
      fallbackNoClaimPath ->
      auditTranscript ->
      result) ->
    result

theorem ay_arpg_replay_contract_intro
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop}
    (hbenchmark : benchmarkFingerprint)
    (harchive : archiveManifestDigest)
    (hscript : replayScriptDigest)
    (hsolver : solverBinaryBuildDigest)
    (hchecker : checkerBinaryVersionDigest)
    (henv : environmentManifest)
    (hcommand : commandLineManifest)
    (houtput : expectedOutputDigest)
    (hartifact : modelProofArtifactDigest)
    (htranscript : checkerTranscript)
    (hfallback : fallbackNoClaimPath)
    (haudit : auditTranscript) :
    ay_arpg_replay_contract
      benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript :=
  fun result k =>
    k hbenchmark harchive hscript hsolver hchecker henv hcommand houtput
      hartifact htranscript hfallback haudit

theorem ay_arpg_replay_contract_benchmark
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg_replay_contract
        benchmarkFingerprint archiveManifestDigest replayScriptDigest
        solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
        commandLineManifest expectedOutputDigest modelProofArtifactDigest
        checkerTranscript fallbackNoClaimPath auditTranscript) :
    benchmarkFingerprint :=
  h benchmarkFingerprint (fun hbenchmark _ _ _ _ _ _ _ _ _ _ _ => hbenchmark)

theorem ay_arpg_replay_contract_archive
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg_replay_contract
        benchmarkFingerprint archiveManifestDigest replayScriptDigest
        solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
        commandLineManifest expectedOutputDigest modelProofArtifactDigest
        checkerTranscript fallbackNoClaimPath auditTranscript) :
    archiveManifestDigest :=
  h archiveManifestDigest (fun _ harchive _ _ _ _ _ _ _ _ _ _ => harchive)

theorem ay_arpg_replay_contract_script
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg_replay_contract
        benchmarkFingerprint archiveManifestDigest replayScriptDigest
        solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
        commandLineManifest expectedOutputDigest modelProofArtifactDigest
        checkerTranscript fallbackNoClaimPath auditTranscript) :
    replayScriptDigest :=
  h replayScriptDigest (fun _ _ hscript _ _ _ _ _ _ _ _ _ => hscript)

theorem ay_arpg_replay_contract_solver
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg_replay_contract
        benchmarkFingerprint archiveManifestDigest replayScriptDigest
        solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
        commandLineManifest expectedOutputDigest modelProofArtifactDigest
        checkerTranscript fallbackNoClaimPath auditTranscript) :
    solverBinaryBuildDigest :=
  h solverBinaryBuildDigest (fun _ _ _ hsolver _ _ _ _ _ _ _ _ => hsolver)

theorem ay_arpg_replay_contract_checker
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg_replay_contract
        benchmarkFingerprint archiveManifestDigest replayScriptDigest
        solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
        commandLineManifest expectedOutputDigest modelProofArtifactDigest
        checkerTranscript fallbackNoClaimPath auditTranscript) :
    checkerBinaryVersionDigest :=
  h checkerBinaryVersionDigest (fun _ _ _ _ hchecker _ _ _ _ _ _ _ => hchecker)

theorem ay_arpg_replay_contract_environment
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg_replay_contract
        benchmarkFingerprint archiveManifestDigest replayScriptDigest
        solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
        commandLineManifest expectedOutputDigest modelProofArtifactDigest
        checkerTranscript fallbackNoClaimPath auditTranscript) :
    environmentManifest :=
  h environmentManifest (fun _ _ _ _ _ henv _ _ _ _ _ _ => henv)

theorem ay_arpg_replay_contract_command
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg_replay_contract
        benchmarkFingerprint archiveManifestDigest replayScriptDigest
        solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
        commandLineManifest expectedOutputDigest modelProofArtifactDigest
        checkerTranscript fallbackNoClaimPath auditTranscript) :
    commandLineManifest :=
  h commandLineManifest (fun _ _ _ _ _ _ hcommand _ _ _ _ _ => hcommand)

theorem ay_arpg_replay_contract_expected_output
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg_replay_contract
        benchmarkFingerprint archiveManifestDigest replayScriptDigest
        solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
        commandLineManifest expectedOutputDigest modelProofArtifactDigest
        checkerTranscript fallbackNoClaimPath auditTranscript) :
    expectedOutputDigest :=
  h expectedOutputDigest (fun _ _ _ _ _ _ _ houtput _ _ _ _ => houtput)

theorem ay_arpg_replay_contract_artifact
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg_replay_contract
        benchmarkFingerprint archiveManifestDigest replayScriptDigest
        solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
        commandLineManifest expectedOutputDigest modelProofArtifactDigest
        checkerTranscript fallbackNoClaimPath auditTranscript) :
    modelProofArtifactDigest :=
  h modelProofArtifactDigest (fun _ _ _ _ _ _ _ _ hartifact _ _ _ => hartifact)

theorem ay_arpg_replay_contract_transcript
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg_replay_contract
        benchmarkFingerprint archiveManifestDigest replayScriptDigest
        solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
        commandLineManifest expectedOutputDigest modelProofArtifactDigest
        checkerTranscript fallbackNoClaimPath auditTranscript) :
    checkerTranscript :=
  h checkerTranscript (fun _ _ _ _ _ _ _ _ _ htranscript _ _ => htranscript)

theorem ay_arpg_replay_contract_fallback
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg_replay_contract
        benchmarkFingerprint archiveManifestDigest replayScriptDigest
        solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
        commandLineManifest expectedOutputDigest modelProofArtifactDigest
        checkerTranscript fallbackNoClaimPath auditTranscript) :
    fallbackNoClaimPath :=
  h fallbackNoClaimPath (fun _ _ _ _ _ _ _ _ _ _ hfallback _ => hfallback)

theorem ay_arpg_replay_contract_audit
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest modelProofArtifactDigest
      checkerTranscript fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg_replay_contract
        benchmarkFingerprint archiveManifestDigest replayScriptDigest
        solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
        commandLineManifest expectedOutputDigest modelProofArtifactDigest
        checkerTranscript fallbackNoClaimPath auditTranscript) :
    auditTranscript :=
  h auditTranscript (fun _ _ _ _ _ _ _ _ _ _ _ haudit => haudit)

def ay_arpg_sat_publication
    (replayContract replayScriptReproduces checkerBackedArtifact checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_arpg_conj replayContract
    (ay_arpg_conj replayScriptReproduces
      (ay_arpg_conj checkerBackedArtifact
        (ay_arpg_conj checkedModel originalBenchmarkSat)))

def ay_arpg_unsat_publication
    (replayContract replayScriptReproduces checkerBackedArtifact checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_arpg_conj replayContract
    (ay_arpg_conj replayScriptReproduces
      (ay_arpg_conj checkerBackedArtifact
        (ay_arpg_conj checkedProof originalBenchmarkUnsat)))

theorem ay_arpg_sat_publication_intro
    {replayContract replayScriptReproduces checkerBackedArtifact checkedModel
      originalBenchmarkSat : Prop}
    (hcontract : replayContract)
    (hreplay : replayScriptReproduces)
    (hartifact : checkerBackedArtifact)
    (hmodel : checkedModel)
    (hsat : originalBenchmarkSat) :
    ay_arpg_sat_publication replayContract replayScriptReproduces
      checkerBackedArtifact checkedModel originalBenchmarkSat :=
  ay_arpg_conj_intro hcontract
    (ay_arpg_conj_intro hreplay
      (ay_arpg_conj_intro hartifact
        (ay_arpg_conj_intro hmodel hsat)))

theorem ay_arpg_unsat_publication_intro
    {replayContract replayScriptReproduces checkerBackedArtifact checkedProof
      originalBenchmarkUnsat : Prop}
    (hcontract : replayContract)
    (hreplay : replayScriptReproduces)
    (hartifact : checkerBackedArtifact)
    (hproof : checkedProof)
    (hunsat : originalBenchmarkUnsat) :
    ay_arpg_unsat_publication replayContract replayScriptReproduces
      checkerBackedArtifact checkedProof originalBenchmarkUnsat :=
  ay_arpg_conj_intro hcontract
    (ay_arpg_conj_intro hreplay
      (ay_arpg_conj_intro hartifact
        (ay_arpg_conj_intro hproof hunsat)))

theorem ay_arpg_sat_requires_replay_contract
    {replayContract replayScriptReproduces checkerBackedArtifact checkedModel
      originalBenchmarkSat : Prop}
    (h :
      ay_arpg_sat_publication replayContract replayScriptReproduces
        checkerBackedArtifact checkedModel originalBenchmarkSat) :
    replayContract :=
  ay_arpg_conj_left h

theorem ay_arpg_sat_requires_replay_script
    {replayContract replayScriptReproduces checkerBackedArtifact checkedModel
      originalBenchmarkSat : Prop}
    (h :
      ay_arpg_sat_publication replayContract replayScriptReproduces
        checkerBackedArtifact checkedModel originalBenchmarkSat) :
    replayScriptReproduces :=
  ay_arpg_conj_left (ay_arpg_conj_right h)

theorem ay_arpg_sat_requires_checker_backed_artifact
    {replayContract replayScriptReproduces checkerBackedArtifact checkedModel
      originalBenchmarkSat : Prop}
    (h :
      ay_arpg_sat_publication replayContract replayScriptReproduces
        checkerBackedArtifact checkedModel originalBenchmarkSat) :
    checkerBackedArtifact :=
  ay_arpg_conj_left (ay_arpg_conj_right (ay_arpg_conj_right h))

theorem ay_arpg_sat_requires_checked_model
    {replayContract replayScriptReproduces checkerBackedArtifact checkedModel
      originalBenchmarkSat : Prop}
    (h :
      ay_arpg_sat_publication replayContract replayScriptReproduces
        checkerBackedArtifact checkedModel originalBenchmarkSat) :
    checkedModel :=
  ay_arpg_conj_left
    (ay_arpg_conj_right (ay_arpg_conj_right (ay_arpg_conj_right h)))

theorem ay_arpg_accepted_replay_preserves_sat_soundness
    {replayContract replayScriptReproduces checkerBackedArtifact checkedModel
      originalBenchmarkSat : Prop}
    (h :
      ay_arpg_sat_publication replayContract replayScriptReproduces
        checkerBackedArtifact checkedModel originalBenchmarkSat) :
    originalBenchmarkSat :=
  ay_arpg_conj_right
    (ay_arpg_conj_right (ay_arpg_conj_right (ay_arpg_conj_right h)))

theorem ay_arpg_unsat_requires_replay_contract
    {replayContract replayScriptReproduces checkerBackedArtifact checkedProof
      originalBenchmarkUnsat : Prop}
    (h :
      ay_arpg_unsat_publication replayContract replayScriptReproduces
        checkerBackedArtifact checkedProof originalBenchmarkUnsat) :
    replayContract :=
  ay_arpg_conj_left h

theorem ay_arpg_unsat_requires_replay_script
    {replayContract replayScriptReproduces checkerBackedArtifact checkedProof
      originalBenchmarkUnsat : Prop}
    (h :
      ay_arpg_unsat_publication replayContract replayScriptReproduces
        checkerBackedArtifact checkedProof originalBenchmarkUnsat) :
    replayScriptReproduces :=
  ay_arpg_conj_left (ay_arpg_conj_right h)

theorem ay_arpg_unsat_requires_checker_backed_artifact
    {replayContract replayScriptReproduces checkerBackedArtifact checkedProof
      originalBenchmarkUnsat : Prop}
    (h :
      ay_arpg_unsat_publication replayContract replayScriptReproduces
        checkerBackedArtifact checkedProof originalBenchmarkUnsat) :
    checkerBackedArtifact :=
  ay_arpg_conj_left (ay_arpg_conj_right (ay_arpg_conj_right h))

theorem ay_arpg_unsat_requires_checked_proof
    {replayContract replayScriptReproduces checkerBackedArtifact checkedProof
      originalBenchmarkUnsat : Prop}
    (h :
      ay_arpg_unsat_publication replayContract replayScriptReproduces
        checkerBackedArtifact checkedProof originalBenchmarkUnsat) :
    checkedProof :=
  ay_arpg_conj_left
    (ay_arpg_conj_right (ay_arpg_conj_right (ay_arpg_conj_right h)))

theorem ay_arpg_accepted_replay_preserves_unsat_soundness
    {replayContract replayScriptReproduces checkerBackedArtifact checkedProof
      originalBenchmarkUnsat : Prop}
    (h :
      ay_arpg_unsat_publication replayContract replayScriptReproduces
        checkerBackedArtifact checkedProof originalBenchmarkUnsat) :
    originalBenchmarkUnsat :=
  ay_arpg_conj_right
    (ay_arpg_conj_right (ay_arpg_conj_right (ay_arpg_conj_right h)))

def ay_arpg_no_claim (diagnostic recompute auditTranscript : Prop) : Prop :=
  ay_arpg_conj diagnostic (ay_arpg_conj recompute auditTranscript)

theorem ay_arpg_no_claim_intro
    {diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : diagnostic)
    (hrecompute : recompute)
    (haudit : auditTranscript) :
    ay_arpg_no_claim diagnostic recompute auditTranscript :=
  ay_arpg_conj_intro hdiagnostic (ay_arpg_conj_intro hrecompute haudit)

theorem ay_arpg_no_claim_diagnostic
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_arpg_no_claim diagnostic recompute auditTranscript) :
    diagnostic :=
  ay_arpg_conj_left h

theorem ay_arpg_no_claim_recompute
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_arpg_no_claim diagnostic recompute auditTranscript) :
    recompute :=
  ay_arpg_conj_left (ay_arpg_conj_right h)

theorem ay_arpg_no_claim_audit
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_arpg_no_claim diagnostic recompute auditTranscript) :
    auditTranscript :=
  ay_arpg_conj_right (ay_arpg_conj_right h)

def ay_arpg_failed_guard
    (mismatch quarantine recompute noClaim auditTranscript : Prop) : Prop :=
  ay_arpg_conj mismatch
    (ay_arpg_conj quarantine
      (ay_arpg_conj recompute (ay_arpg_conj noClaim auditTranscript)))

theorem ay_arpg_failed_guard_intro
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (hmismatch : mismatch)
    (hquarantine : quarantine)
    (hrecompute : recompute)
    (hnoclaim : noClaim)
    (haudit : auditTranscript) :
    ay_arpg_failed_guard mismatch quarantine recompute noClaim auditTranscript :=
  ay_arpg_conj_intro hmismatch
    (ay_arpg_conj_intro hquarantine
      (ay_arpg_conj_intro hrecompute (ay_arpg_conj_intro hnoclaim haudit)))

theorem ay_arpg_failed_guard_mismatch
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h :
      ay_arpg_failed_guard mismatch quarantine recompute noClaim
        auditTranscript) :
    mismatch :=
  ay_arpg_conj_left h

theorem ay_arpg_failed_guard_recompute
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h :
      ay_arpg_failed_guard mismatch quarantine recompute noClaim
        auditTranscript) :
    recompute :=
  ay_arpg_conj_left (ay_arpg_conj_right (ay_arpg_conj_right h))

theorem ay_arpg_failed_guard_no_claim
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h :
      ay_arpg_failed_guard mismatch quarantine recompute noClaim
        auditTranscript) :
    noClaim :=
  ay_arpg_conj_left
    (ay_arpg_conj_right (ay_arpg_conj_right (ay_arpg_conj_right h)))

theorem ay_arpg_failed_guard_audit
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h :
      ay_arpg_failed_guard mismatch quarantine recompute noClaim
        auditTranscript) :
    auditTranscript :=
  ay_arpg_conj_right
    (ay_arpg_conj_right (ay_arpg_conj_right (ay_arpg_conj_right h)))

def ay_arpg_blocks_sat (noClaim publicSat : Prop) : Prop :=
  publicSat -> noClaim

def ay_arpg_blocks_unsat (noClaim publicUnsat : Prop) : Prop :=
  publicUnsat -> noClaim

theorem ay_arpg_failed_guard_cannot_bless_sat
    {mismatch quarantine recompute noClaim auditTranscript publicSat : Prop}
    (h :
      ay_arpg_failed_guard mismatch quarantine recompute noClaim
        auditTranscript) :
    ay_arpg_blocks_sat noClaim publicSat :=
  fun _ => ay_arpg_failed_guard_no_claim h

theorem ay_arpg_failed_guard_cannot_bless_unsat
    {mismatch quarantine recompute noClaim auditTranscript publicUnsat : Prop}
    (h :
      ay_arpg_failed_guard mismatch quarantine recompute noClaim
        auditTranscript) :
    ay_arpg_blocks_unsat noClaim publicUnsat :=
  fun _ => ay_arpg_failed_guard_no_claim h

def ay_arpg_mismatch_forces_no_claim
    (mismatch diagnostic recompute auditTranscript : Prop) : Prop :=
  mismatch -> ay_arpg_no_claim diagnostic recompute auditTranscript

theorem ay_arpg_mismatch_forces_no_claim_intro
    {mismatch diagnostic recompute auditTranscript : Prop}
    (h : mismatch -> diagnostic)
    (hrecompute : mismatch -> recompute)
    (haudit : mismatch -> auditTranscript) :
    ay_arpg_mismatch_forces_no_claim mismatch diagnostic recompute
      auditTranscript :=
  fun hmismatch =>
    ay_arpg_no_claim_intro (h hmismatch) (hrecompute hmismatch)
      (haudit hmismatch)

theorem ay_arpg_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : archiveMismatch -> diagnostic)
    (hrecompute : archiveMismatch -> recompute)
    (haudit : archiveMismatch -> auditTranscript) :
    ay_arpg_mismatch_forces_no_claim archiveMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg_script_mismatch_forces_no_claim
    {scriptMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : scriptMismatch -> diagnostic)
    (hrecompute : scriptMismatch -> recompute)
    (haudit : scriptMismatch -> auditTranscript) :
    ay_arpg_mismatch_forces_no_claim scriptMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg_build_mismatch_forces_no_claim
    {buildMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : buildMismatch -> diagnostic)
    (hrecompute : buildMismatch -> recompute)
    (haudit : buildMismatch -> auditTranscript) :
    ay_arpg_mismatch_forces_no_claim buildMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg_checker_mismatch_forces_no_claim
    {checkerMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : checkerMismatch -> diagnostic)
    (hrecompute : checkerMismatch -> recompute)
    (haudit : checkerMismatch -> auditTranscript) :
    ay_arpg_mismatch_forces_no_claim checkerMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg_environment_mismatch_forces_no_claim
    {environmentMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : environmentMismatch -> diagnostic)
    (hrecompute : environmentMismatch -> recompute)
    (haudit : environmentMismatch -> auditTranscript) :
    ay_arpg_mismatch_forces_no_claim environmentMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg_command_mismatch_forces_no_claim
    {commandMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : commandMismatch -> diagnostic)
    (hrecompute : commandMismatch -> recompute)
    (haudit : commandMismatch -> auditTranscript) :
    ay_arpg_mismatch_forces_no_claim commandMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg_output_mismatch_forces_no_claim
    {outputMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : outputMismatch -> diagnostic)
    (hrecompute : outputMismatch -> recompute)
    (haudit : outputMismatch -> auditTranscript) :
    ay_arpg_mismatch_forces_no_claim outputMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg_artifact_mismatch_forces_no_claim
    {artifactMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : artifactMismatch -> diagnostic)
    (hrecompute : artifactMismatch -> recompute)
    (haudit : artifactMismatch -> auditTranscript) :
    ay_arpg_mismatch_forces_no_claim artifactMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg_transcript_mismatch_forces_no_claim
    {transcriptMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : transcriptMismatch -> diagnostic)
    (hrecompute : transcriptMismatch -> recompute)
    (haudit : transcriptMismatch -> auditTranscript) :
    ay_arpg_mismatch_forces_no_claim transcriptMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

def ay_arpg_script_only_evidence
    (benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest fallbackNoClaimPath
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkFingerprint ->
      archiveManifestDigest ->
      replayScriptDigest ->
      solverBinaryBuildDigest ->
      checkerBinaryVersionDigest ->
      environmentManifest ->
      commandLineManifest ->
      expectedOutputDigest ->
      fallbackNoClaimPath ->
      auditTranscript ->
      result) ->
    result

theorem ay_arpg_script_only_evidence_intro
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest fallbackNoClaimPath
      auditTranscript : Prop}
    (hbenchmark : benchmarkFingerprint)
    (harchive : archiveManifestDigest)
    (hscript : replayScriptDigest)
    (hsolver : solverBinaryBuildDigest)
    (hchecker : checkerBinaryVersionDigest)
    (henv : environmentManifest)
    (hcommand : commandLineManifest)
    (houtput : expectedOutputDigest)
    (hfallback : fallbackNoClaimPath)
    (haudit : auditTranscript) :
    ay_arpg_script_only_evidence benchmarkFingerprint archiveManifestDigest
      replayScriptDigest solverBinaryBuildDigest checkerBinaryVersionDigest
      environmentManifest commandLineManifest expectedOutputDigest
      fallbackNoClaimPath auditTranscript :=
  fun result k =>
    k hbenchmark harchive hscript hsolver hchecker henv hcommand houtput
      hfallback haudit

theorem ay_arpg_replay_script_alone_cannot_publish_sat
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest fallbackNoClaimPath
      auditTranscript noClaim publicSat : Prop}
    (h :
      ay_arpg_script_only_evidence benchmarkFingerprint archiveManifestDigest
        replayScriptDigest solverBinaryBuildDigest checkerBinaryVersionDigest
        environmentManifest commandLineManifest expectedOutputDigest
        fallbackNoClaimPath auditTranscript)
    (hnoClaim : fallbackNoClaimPath -> noClaim) :
    ay_arpg_blocks_sat noClaim publicSat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

theorem ay_arpg_replay_script_alone_cannot_publish_unsat
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest fallbackNoClaimPath
      auditTranscript noClaim publicUnsat : Prop}
    (h :
      ay_arpg_script_only_evidence benchmarkFingerprint archiveManifestDigest
        replayScriptDigest solverBinaryBuildDigest checkerBinaryVersionDigest
        environmentManifest commandLineManifest expectedOutputDigest
        fallbackNoClaimPath auditTranscript)
    (hnoClaim : fallbackNoClaimPath -> noClaim) :
    ay_arpg_blocks_unsat noClaim publicUnsat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

theorem ay_arpg_script_only_lacks_checker_artifact
    {benchmarkFingerprint archiveManifestDigest replayScriptDigest
      solverBinaryBuildDigest checkerBinaryVersionDigest environmentManifest
      commandLineManifest expectedOutputDigest fallbackNoClaimPath
      auditTranscript checkerBackedArtifact noClaim : Prop}
    (h :
      ay_arpg_script_only_evidence benchmarkFingerprint archiveManifestDigest
        replayScriptDigest solverBinaryBuildDigest checkerBinaryVersionDigest
        environmentManifest commandLineManifest expectedOutputDigest
        fallbackNoClaimPath auditTranscript)
    (hnoClaim : fallbackNoClaimPath -> noClaim) :
    checkerBackedArtifact -> noClaim :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

theorem ay_arpg_accepted_publication_tied_to_replayable_archive
    {replayContract replayScriptReproduces checkerBackedArtifact checkedModel
      originalBenchmarkSat replayableArchive : Prop}
    (hreplayable :
      replayContract -> replayScriptReproduces -> checkerBackedArtifact ->
        replayableArchive)
    (h :
      ay_arpg_sat_publication replayContract replayScriptReproduces
        checkerBackedArtifact checkedModel originalBenchmarkSat) :
    replayableArchive :=
  hreplayable
    (ay_arpg_sat_requires_replay_contract h)
    (ay_arpg_sat_requires_replay_script h)
    (ay_arpg_sat_requires_checker_backed_artifact h)

theorem ay_arpg_accepted_unsat_publication_tied_to_replayable_archive
    {replayContract replayScriptReproduces checkerBackedArtifact checkedProof
      originalBenchmarkUnsat replayableArchive : Prop}
    (hreplayable :
      replayContract -> replayScriptReproduces -> checkerBackedArtifact ->
        replayableArchive)
    (h :
      ay_arpg_unsat_publication replayContract replayScriptReproduces
        checkerBackedArtifact checkedProof originalBenchmarkUnsat) :
    replayableArchive :=
  hreplayable
    (ay_arpg_unsat_requires_replay_contract h)
    (ay_arpg_unsat_requires_replay_script h)
    (ay_arpg_unsat_requires_checker_backed_artifact h)
