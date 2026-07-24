-- Artifact retention policy guard for sequential-main SAT-COMP validation.
-- Self-contained propositional contract for retained, deleted, and quarantined
-- ay result artifacts.

def ay_arpg2_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_arpg2_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

theorem ay_arpg2_conj_intro {left right : Prop} (hleft : left) (hright : right) :
    ay_arpg2_conj left right :=
  fun result k => k hleft hright

theorem ay_arpg2_conj_left {left right : Prop} (h : ay_arpg2_conj left right) :
    left :=
  h left (fun hleft _ => hleft)

theorem ay_arpg2_conj_right {left right : Prop} (h : ay_arpg2_conj left right) :
    right :=
  h right (fun _ hright => hright)

theorem ay_arpg2_disj_left {left right : Prop} (hleft : left) :
    ay_arpg2_disj left right :=
  fun result kleft _ => kleft hleft

theorem ay_arpg2_disj_right {left right : Prop} (hright : right) :
    ay_arpg2_disj left right :=
  fun result _ kright => kright hright

def ay_arpg2_retention_contract
    (benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkFingerprint ->
      resultStatusDigest ->
      modelProofArtifactDigestOptions ->
      checkerTranscriptDigest ->
      retentionPolicyManifest ->
      quarantineLedger ->
      archivePathMap ->
      deletionLedger ->
      resultBundleDigest ->
      solverBuildEvidence ->
      fallbackNoClaimPath ->
      auditTranscript ->
      result) ->
    result

theorem ay_arpg2_retention_contract_intro
    {benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (hbenchmark : benchmarkFingerprint)
    (hstatus : resultStatusDigest)
    (hartifacts : modelProofArtifactDigestOptions)
    (hchecker : checkerTranscriptDigest)
    (hpolicy : retentionPolicyManifest)
    (hquarantine : quarantineLedger)
    (hpaths : archivePathMap)
    (hdeletions : deletionLedger)
    (hbundle : resultBundleDigest)
    (hbuild : solverBuildEvidence)
    (hfallback : fallbackNoClaimPath)
    (haudit : auditTranscript) :
    ay_arpg2_retention_contract benchmarkFingerprint resultStatusDigest
      modelProofArtifactDigestOptions checkerTranscriptDigest
      retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
      resultBundleDigest solverBuildEvidence fallbackNoClaimPath
      auditTranscript :=
  fun result k =>
    k hbenchmark hstatus hartifacts hchecker hpolicy hquarantine hpaths
      hdeletions hbundle hbuild hfallback haudit

theorem ay_arpg2_contract_benchmark
    {benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg2_retention_contract benchmarkFingerprint resultStatusDigest
        modelProofArtifactDigestOptions checkerTranscriptDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        resultBundleDigest solverBuildEvidence fallbackNoClaimPath
        auditTranscript) :
    benchmarkFingerprint :=
  h benchmarkFingerprint (fun hbenchmark _ _ _ _ _ _ _ _ _ _ _ => hbenchmark)

theorem ay_arpg2_contract_status
    {benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg2_retention_contract benchmarkFingerprint resultStatusDigest
        modelProofArtifactDigestOptions checkerTranscriptDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        resultBundleDigest solverBuildEvidence fallbackNoClaimPath
        auditTranscript) :
    resultStatusDigest :=
  h resultStatusDigest (fun _ hstatus _ _ _ _ _ _ _ _ _ _ => hstatus)

theorem ay_arpg2_contract_artifact_options
    {benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg2_retention_contract benchmarkFingerprint resultStatusDigest
        modelProofArtifactDigestOptions checkerTranscriptDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        resultBundleDigest solverBuildEvidence fallbackNoClaimPath
        auditTranscript) :
    modelProofArtifactDigestOptions :=
  h modelProofArtifactDigestOptions (fun _ _ hartifacts _ _ _ _ _ _ _ _ _ => hartifacts)

theorem ay_arpg2_contract_checker_transcript
    {benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg2_retention_contract benchmarkFingerprint resultStatusDigest
        modelProofArtifactDigestOptions checkerTranscriptDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        resultBundleDigest solverBuildEvidence fallbackNoClaimPath
        auditTranscript) :
    checkerTranscriptDigest :=
  h checkerTranscriptDigest (fun _ _ _ hchecker _ _ _ _ _ _ _ _ => hchecker)

theorem ay_arpg2_contract_policy
    {benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg2_retention_contract benchmarkFingerprint resultStatusDigest
        modelProofArtifactDigestOptions checkerTranscriptDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        resultBundleDigest solverBuildEvidence fallbackNoClaimPath
        auditTranscript) :
    retentionPolicyManifest :=
  h retentionPolicyManifest (fun _ _ _ _ hpolicy _ _ _ _ _ _ _ => hpolicy)

theorem ay_arpg2_contract_quarantine
    {benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg2_retention_contract benchmarkFingerprint resultStatusDigest
        modelProofArtifactDigestOptions checkerTranscriptDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        resultBundleDigest solverBuildEvidence fallbackNoClaimPath
        auditTranscript) :
    quarantineLedger :=
  h quarantineLedger (fun _ _ _ _ _ hquarantine _ _ _ _ _ _ => hquarantine)

theorem ay_arpg2_contract_archive_paths
    {benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg2_retention_contract benchmarkFingerprint resultStatusDigest
        modelProofArtifactDigestOptions checkerTranscriptDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        resultBundleDigest solverBuildEvidence fallbackNoClaimPath
        auditTranscript) :
    archivePathMap :=
  h archivePathMap (fun _ _ _ _ _ _ hpaths _ _ _ _ _ => hpaths)

theorem ay_arpg2_contract_deletions
    {benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg2_retention_contract benchmarkFingerprint resultStatusDigest
        modelProofArtifactDigestOptions checkerTranscriptDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        resultBundleDigest solverBuildEvidence fallbackNoClaimPath
        auditTranscript) :
    deletionLedger :=
  h deletionLedger (fun _ _ _ _ _ _ _ hdeletions _ _ _ _ => hdeletions)

theorem ay_arpg2_contract_result_bundle
    {benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg2_retention_contract benchmarkFingerprint resultStatusDigest
        modelProofArtifactDigestOptions checkerTranscriptDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        resultBundleDigest solverBuildEvidence fallbackNoClaimPath
        auditTranscript) :
    resultBundleDigest :=
  h resultBundleDigest (fun _ _ _ _ _ _ _ _ hbundle _ _ _ => hbundle)

theorem ay_arpg2_contract_build
    {benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg2_retention_contract benchmarkFingerprint resultStatusDigest
        modelProofArtifactDigestOptions checkerTranscriptDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        resultBundleDigest solverBuildEvidence fallbackNoClaimPath
        auditTranscript) :
    solverBuildEvidence :=
  h solverBuildEvidence (fun _ _ _ _ _ _ _ _ _ hbuild _ _ => hbuild)

theorem ay_arpg2_contract_fallback
    {benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg2_retention_contract benchmarkFingerprint resultStatusDigest
        modelProofArtifactDigestOptions checkerTranscriptDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        resultBundleDigest solverBuildEvidence fallbackNoClaimPath
        auditTranscript) :
    fallbackNoClaimPath :=
  h fallbackNoClaimPath (fun _ _ _ _ _ _ _ _ _ _ hfallback _ => hfallback)

theorem ay_arpg2_contract_audit
    {benchmarkFingerprint resultStatusDigest modelProofArtifactDigestOptions
      checkerTranscriptDigest retentionPolicyManifest quarantineLedger
      archivePathMap deletionLedger resultBundleDigest solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (h :
      ay_arpg2_retention_contract benchmarkFingerprint resultStatusDigest
        modelProofArtifactDigestOptions checkerTranscriptDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        resultBundleDigest solverBuildEvidence fallbackNoClaimPath
        auditTranscript) :
    auditTranscript :=
  h auditTranscript (fun _ _ _ _ _ _ _ _ _ _ _ haudit => haudit)

def ay_arpg2_retained_publication
    (retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      resultKindMatches originalBenchmarkClaim : Prop) : Prop :=
  ay_arpg2_conj retentionContract
    (ay_arpg2_conj retainedArtifactMatchesBundle
      (ay_arpg2_conj checkerBackedBundle
        (ay_arpg2_conj resultKindMatches originalBenchmarkClaim)))

def ay_arpg2_sat_publication
    (retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      checkedModel originalBenchmarkSat : Prop) : Prop :=
  ay_arpg2_retained_publication retentionContract retainedArtifactMatchesBundle
    checkerBackedBundle checkedModel originalBenchmarkSat

def ay_arpg2_unsat_publication
    (retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      checkedProof originalBenchmarkUnsat : Prop) : Prop :=
  ay_arpg2_retained_publication retentionContract retainedArtifactMatchesBundle
    checkerBackedBundle checkedProof originalBenchmarkUnsat

theorem ay_arpg2_retained_publication_intro
    {retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      resultKindMatches originalBenchmarkClaim : Prop}
    (hcontract : retentionContract)
    (hretained : retainedArtifactMatchesBundle)
    (hchecker : checkerBackedBundle)
    (hkind : resultKindMatches)
    (hclaim : originalBenchmarkClaim) :
    ay_arpg2_retained_publication retentionContract retainedArtifactMatchesBundle
      checkerBackedBundle resultKindMatches originalBenchmarkClaim :=
  ay_arpg2_conj_intro hcontract
    (ay_arpg2_conj_intro hretained
      (ay_arpg2_conj_intro hchecker (ay_arpg2_conj_intro hkind hclaim)))

theorem ay_arpg2_sat_publication_intro
    {retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      checkedModel originalBenchmarkSat : Prop}
    (hcontract : retentionContract)
    (hretained : retainedArtifactMatchesBundle)
    (hchecker : checkerBackedBundle)
    (hmodel : checkedModel)
    (hsat : originalBenchmarkSat) :
    ay_arpg2_sat_publication retentionContract retainedArtifactMatchesBundle
      checkerBackedBundle checkedModel originalBenchmarkSat :=
  ay_arpg2_retained_publication_intro hcontract hretained hchecker hmodel hsat

theorem ay_arpg2_unsat_publication_intro
    {retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      checkedProof originalBenchmarkUnsat : Prop}
    (hcontract : retentionContract)
    (hretained : retainedArtifactMatchesBundle)
    (hchecker : checkerBackedBundle)
    (hproof : checkedProof)
    (hunsat : originalBenchmarkUnsat) :
    ay_arpg2_unsat_publication retentionContract retainedArtifactMatchesBundle
      checkerBackedBundle checkedProof originalBenchmarkUnsat :=
  ay_arpg2_retained_publication_intro hcontract hretained hchecker hproof hunsat

theorem ay_arpg2_retained_publication_contract
    {retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_arpg2_retained_publication retentionContract retainedArtifactMatchesBundle
        checkerBackedBundle resultKindMatches originalBenchmarkClaim) :
    retentionContract :=
  ay_arpg2_conj_left h

theorem ay_arpg2_retained_publication_artifact_matches_bundle
    {retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_arpg2_retained_publication retentionContract retainedArtifactMatchesBundle
        checkerBackedBundle resultKindMatches originalBenchmarkClaim) :
    retainedArtifactMatchesBundle :=
  ay_arpg2_conj_left (ay_arpg2_conj_right h)

theorem ay_arpg2_retained_publication_checker_backed
    {retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_arpg2_retained_publication retentionContract retainedArtifactMatchesBundle
        checkerBackedBundle resultKindMatches originalBenchmarkClaim) :
    checkerBackedBundle :=
  ay_arpg2_conj_left (ay_arpg2_conj_right (ay_arpg2_conj_right h))

theorem ay_arpg2_retained_publication_result_kind
    {retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_arpg2_retained_publication retentionContract retainedArtifactMatchesBundle
        checkerBackedBundle resultKindMatches originalBenchmarkClaim) :
    resultKindMatches :=
  ay_arpg2_conj_left
    (ay_arpg2_conj_right (ay_arpg2_conj_right (ay_arpg2_conj_right h)))

theorem ay_arpg2_retained_publication_claim
    {retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_arpg2_retained_publication retentionContract retainedArtifactMatchesBundle
        checkerBackedBundle resultKindMatches originalBenchmarkClaim) :
    originalBenchmarkClaim :=
  ay_arpg2_conj_right
    (ay_arpg2_conj_right (ay_arpg2_conj_right (ay_arpg2_conj_right h)))

theorem ay_arpg2_retained_artifacts_match_checker_bundle
    {retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_arpg2_retained_publication retentionContract retainedArtifactMatchesBundle
        checkerBackedBundle resultKindMatches originalBenchmarkClaim) :
    retainedArtifactMatchesBundle :=
  ay_arpg2_retained_publication_artifact_matches_bundle h

theorem ay_arpg2_retained_artifacts_have_checker_backed_bundle
    {retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      resultKindMatches originalBenchmarkClaim : Prop}
    (h :
      ay_arpg2_retained_publication retentionContract retainedArtifactMatchesBundle
        checkerBackedBundle resultKindMatches originalBenchmarkClaim) :
    checkerBackedBundle :=
  ay_arpg2_retained_publication_checker_backed h

theorem ay_arpg2_accepted_sat_preserves_soundness
    {retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      checkedModel originalBenchmarkSat : Prop}
    (h :
      ay_arpg2_sat_publication retentionContract retainedArtifactMatchesBundle
        checkerBackedBundle checkedModel originalBenchmarkSat) :
    originalBenchmarkSat :=
  ay_arpg2_retained_publication_claim h

theorem ay_arpg2_accepted_unsat_preserves_soundness
    {retentionContract retainedArtifactMatchesBundle checkerBackedBundle
      checkedProof originalBenchmarkUnsat : Prop}
    (h :
      ay_arpg2_unsat_publication retentionContract retainedArtifactMatchesBundle
        checkerBackedBundle checkedProof originalBenchmarkUnsat) :
    originalBenchmarkUnsat :=
  ay_arpg2_retained_publication_claim h

def ay_arpg2_no_claim (diagnostic recompute auditTranscript : Prop) : Prop :=
  ay_arpg2_conj diagnostic (ay_arpg2_conj recompute auditTranscript)

theorem ay_arpg2_no_claim_intro
    {diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : diagnostic)
    (hrecompute : recompute)
    (haudit : auditTranscript) :
    ay_arpg2_no_claim diagnostic recompute auditTranscript :=
  ay_arpg2_conj_intro hdiagnostic (ay_arpg2_conj_intro hrecompute haudit)

theorem ay_arpg2_no_claim_diagnostic
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_arpg2_no_claim diagnostic recompute auditTranscript) :
    diagnostic :=
  ay_arpg2_conj_left h

theorem ay_arpg2_no_claim_recompute
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_arpg2_no_claim diagnostic recompute auditTranscript) :
    recompute :=
  ay_arpg2_conj_left (ay_arpg2_conj_right h)

theorem ay_arpg2_no_claim_audit
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_arpg2_no_claim diagnostic recompute auditTranscript) :
    auditTranscript :=
  ay_arpg2_conj_right (ay_arpg2_conj_right h)

def ay_arpg2_mismatch_forces_no_claim
    (mismatch diagnostic recompute auditTranscript : Prop) : Prop :=
  mismatch -> ay_arpg2_no_claim diagnostic recompute auditTranscript

theorem ay_arpg2_mismatch_forces_no_claim_intro
    {mismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : mismatch -> diagnostic)
    (hrecompute : mismatch -> recompute)
    (haudit : mismatch -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim mismatch diagnostic recompute
      auditTranscript :=
  fun hmismatch =>
    ay_arpg2_no_claim_intro (hdiagnostic hmismatch) (hrecompute hmismatch)
      (haudit hmismatch)

theorem ay_arpg2_stale_artifact_forces_no_claim
    {staleArtifact diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : staleArtifact -> diagnostic)
    (hrecompute : staleArtifact -> recompute)
    (haudit : staleArtifact -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim staleArtifact diagnostic recompute
      auditTranscript :=
  ay_arpg2_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg2_wrong_kind_artifact_forces_no_claim
    {wrongKindArtifact diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : wrongKindArtifact -> diagnostic)
    (hrecompute : wrongKindArtifact -> recompute)
    (haudit : wrongKindArtifact -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim wrongKindArtifact diagnostic recompute
      auditTranscript :=
  ay_arpg2_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg2_missing_artifact_forces_no_claim
    {missingArtifact diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : missingArtifact -> diagnostic)
    (hrecompute : missingArtifact -> recompute)
    (haudit : missingArtifact -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim missingArtifact diagnostic recompute
      auditTranscript :=
  ay_arpg2_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg2_deleted_artifact_forces_no_claim
    {deletedArtifact diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : deletedArtifact -> diagnostic)
    (hrecompute : deletedArtifact -> recompute)
    (haudit : deletedArtifact -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim deletedArtifact diagnostic recompute
      auditTranscript :=
  ay_arpg2_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg2_quarantined_artifact_no_claim
    {quarantineEvidence diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : quarantineEvidence -> diagnostic)
    (hrecompute : quarantineEvidence -> recompute)
    (haudit : quarantineEvidence -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim quarantineEvidence diagnostic recompute
      auditTranscript :=
  ay_arpg2_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg2_policy_mismatch_forces_no_claim
    {policyMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : policyMismatch -> diagnostic)
    (hrecompute : policyMismatch -> recompute)
    (haudit : policyMismatch -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim policyMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg2_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg2_quarantine_mismatch_forces_no_claim
    {quarantineMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : quarantineMismatch -> diagnostic)
    (hrecompute : quarantineMismatch -> recompute)
    (haudit : quarantineMismatch -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim quarantineMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg2_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg2_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : archiveMismatch -> diagnostic)
    (hrecompute : archiveMismatch -> recompute)
    (haudit : archiveMismatch -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim archiveMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg2_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg2_deletion_mismatch_forces_no_claim
    {deletionMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : deletionMismatch -> diagnostic)
    (hrecompute : deletionMismatch -> recompute)
    (haudit : deletionMismatch -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim deletionMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg2_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg2_bundle_mismatch_forces_no_claim
    {bundleMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : bundleMismatch -> diagnostic)
    (hrecompute : bundleMismatch -> recompute)
    (haudit : bundleMismatch -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim bundleMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg2_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg2_checker_mismatch_forces_no_claim
    {checkerMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : checkerMismatch -> diagnostic)
    (hrecompute : checkerMismatch -> recompute)
    (haudit : checkerMismatch -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim checkerMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg2_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg2_build_mismatch_forces_no_claim
    {buildMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : buildMismatch -> diagnostic)
    (hrecompute : buildMismatch -> recompute)
    (haudit : buildMismatch -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim buildMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg2_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_arpg2_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : auditMismatch -> diagnostic)
    (hrecompute : auditMismatch -> recompute)
    (haudit : auditMismatch -> auditTranscript) :
    ay_arpg2_mismatch_forces_no_claim auditMismatch diagnostic recompute
      auditTranscript :=
  ay_arpg2_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

def ay_arpg2_retention_metadata_only
    (benchmarkFingerprint resultStatusDigest retentionPolicyManifest
      quarantineLedger archivePathMap deletionLedger solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkFingerprint ->
      resultStatusDigest ->
      retentionPolicyManifest ->
      quarantineLedger ->
      archivePathMap ->
      deletionLedger ->
      solverBuildEvidence ->
      fallbackNoClaimPath ->
      auditTranscript ->
      result) ->
    result

theorem ay_arpg2_retention_metadata_only_intro
    {benchmarkFingerprint resultStatusDigest retentionPolicyManifest
      quarantineLedger archivePathMap deletionLedger solverBuildEvidence
      fallbackNoClaimPath auditTranscript : Prop}
    (hbenchmark : benchmarkFingerprint)
    (hstatus : resultStatusDigest)
    (hpolicy : retentionPolicyManifest)
    (hquarantine : quarantineLedger)
    (hpaths : archivePathMap)
    (hdeletions : deletionLedger)
    (hbuild : solverBuildEvidence)
    (hfallback : fallbackNoClaimPath)
    (haudit : auditTranscript) :
    ay_arpg2_retention_metadata_only benchmarkFingerprint resultStatusDigest
      retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
      solverBuildEvidence fallbackNoClaimPath auditTranscript :=
  fun result k =>
    k hbenchmark hstatus hpolicy hquarantine hpaths hdeletions hbuild
      hfallback haudit

def ay_arpg2_blocks_sat (noClaim publicSat : Prop) : Prop :=
  publicSat -> noClaim

def ay_arpg2_blocks_unsat (noClaim publicUnsat : Prop) : Prop :=
  publicUnsat -> noClaim

theorem ay_arpg2_retention_metadata_alone_cannot_publish_sat
    {benchmarkFingerprint resultStatusDigest retentionPolicyManifest
      quarantineLedger archivePathMap deletionLedger solverBuildEvidence
      fallbackNoClaimPath auditTranscript noClaim publicSat : Prop}
    (h :
      ay_arpg2_retention_metadata_only benchmarkFingerprint resultStatusDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        solverBuildEvidence fallbackNoClaimPath auditTranscript)
    (hnoClaim : fallbackNoClaimPath -> noClaim) :
    ay_arpg2_blocks_sat noClaim publicSat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

theorem ay_arpg2_retention_metadata_alone_cannot_publish_unsat
    {benchmarkFingerprint resultStatusDigest retentionPolicyManifest
      quarantineLedger archivePathMap deletionLedger solverBuildEvidence
      fallbackNoClaimPath auditTranscript noClaim publicUnsat : Prop}
    (h :
      ay_arpg2_retention_metadata_only benchmarkFingerprint resultStatusDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        solverBuildEvidence fallbackNoClaimPath auditTranscript)
    (hnoClaim : fallbackNoClaimPath -> noClaim) :
    ay_arpg2_blocks_unsat noClaim publicUnsat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

theorem ay_arpg2_retention_metadata_only_lacks_checker_bundle
    {benchmarkFingerprint resultStatusDigest retentionPolicyManifest
      quarantineLedger archivePathMap deletionLedger solverBuildEvidence
      fallbackNoClaimPath auditTranscript checkerBackedBundle noClaim : Prop}
    (h :
      ay_arpg2_retention_metadata_only benchmarkFingerprint resultStatusDigest
        retentionPolicyManifest quarantineLedger archivePathMap deletionLedger
        solverBuildEvidence fallbackNoClaimPath auditTranscript)
    (hnoClaim : fallbackNoClaimPath -> noClaim) :
    checkerBackedBundle -> noClaim :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

def ay_arpg2_failed_guard
    (mismatch quarantine recompute noClaim auditTranscript : Prop) : Prop :=
  ay_arpg2_conj mismatch
    (ay_arpg2_conj quarantine
      (ay_arpg2_conj recompute (ay_arpg2_conj noClaim auditTranscript)))

theorem ay_arpg2_failed_guard_intro
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (hmismatch : mismatch)
    (hquarantine : quarantine)
    (hrecompute : recompute)
    (hnoclaim : noClaim)
    (haudit : auditTranscript) :
    ay_arpg2_failed_guard mismatch quarantine recompute noClaim auditTranscript :=
  ay_arpg2_conj_intro hmismatch
    (ay_arpg2_conj_intro hquarantine
      (ay_arpg2_conj_intro hrecompute (ay_arpg2_conj_intro hnoclaim haudit)))

theorem ay_arpg2_failed_guard_mismatch
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h :
      ay_arpg2_failed_guard mismatch quarantine recompute noClaim
        auditTranscript) :
    mismatch :=
  ay_arpg2_conj_left h

theorem ay_arpg2_failed_guard_recompute
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h :
      ay_arpg2_failed_guard mismatch quarantine recompute noClaim
        auditTranscript) :
    recompute :=
  ay_arpg2_conj_left (ay_arpg2_conj_right (ay_arpg2_conj_right h))

theorem ay_arpg2_failed_guard_no_claim
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h :
      ay_arpg2_failed_guard mismatch quarantine recompute noClaim
        auditTranscript) :
    noClaim :=
  ay_arpg2_conj_left
    (ay_arpg2_conj_right (ay_arpg2_conj_right (ay_arpg2_conj_right h)))

theorem ay_arpg2_failed_guard_audit
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h :
      ay_arpg2_failed_guard mismatch quarantine recompute noClaim
        auditTranscript) :
    auditTranscript :=
  ay_arpg2_conj_right
    (ay_arpg2_conj_right (ay_arpg2_conj_right (ay_arpg2_conj_right h)))

theorem ay_arpg2_failed_retention_guard_cannot_bless_sat
    {mismatch quarantine recompute noClaim auditTranscript publicSat : Prop}
    (h :
      ay_arpg2_failed_guard mismatch quarantine recompute noClaim
        auditTranscript) :
    ay_arpg2_blocks_sat noClaim publicSat :=
  fun _ => ay_arpg2_failed_guard_no_claim h

theorem ay_arpg2_failed_retention_guard_cannot_bless_unsat
    {mismatch quarantine recompute noClaim auditTranscript publicUnsat : Prop}
    (h :
      ay_arpg2_failed_guard mismatch quarantine recompute noClaim
        auditTranscript) :
    ay_arpg2_blocks_unsat noClaim publicUnsat :=
  fun _ => ay_arpg2_failed_guard_no_claim h

theorem ay_arpg2_failed_guard_forces_recompute
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h :
      ay_arpg2_failed_guard mismatch quarantine recompute noClaim
        auditTranscript) :
    recompute :=
  ay_arpg2_failed_guard_recompute h
