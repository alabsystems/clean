-- Checker-version upgrade guard for sequential-main SAT-COMP validation.
-- Self-contained propositional contract for revalidating ay result bundles
-- after model/proof checker or checker-flag changes.

def ay_cvug_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cvug_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

theorem ay_cvug_conj_intro {left right : Prop} (hleft : left) (hright : right) :
    ay_cvug_conj left right :=
  fun result k => k hleft hright

theorem ay_cvug_conj_left {left right : Prop} (h : ay_cvug_conj left right) :
    left :=
  h left (fun hleft _ => hleft)

theorem ay_cvug_conj_right {left right : Prop} (h : ay_cvug_conj left right) :
    right :=
  h right (fun _ hright => hright)

theorem ay_cvug_disj_left {left right : Prop} (hleft : left) :
    ay_cvug_disj left right :=
  fun result kleft _ => kleft hleft

theorem ay_cvug_disj_right {left right : Prop} (hright : right) :
    ay_cvug_disj left right :=
  fun result _ kright => kright hright

def ay_cvug_upgrade_contract
    (benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop) :
    Prop :=
  forall result : Prop,
    (benchmarkFingerprint ->
      artifactDigest ->
      oldCheckerVersionDigest ->
      newCheckerVersionDigest ->
      checkerFlagManifest ->
      transcriptCompatibilityWitness ->
      freshRecheckTranscriptDigest ->
      invalidationLedger ->
      resultBundleDigest ->
      archiveManifest ->
      fallbackRecomputeNoClaimPath ->
      auditTranscript ->
      result) ->
    result

theorem ay_cvug_upgrade_contract_intro
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (hbenchmark : benchmarkFingerprint)
    (hartifact : artifactDigest)
    (holdchecker : oldCheckerVersionDigest)
    (hnewchecker : newCheckerVersionDigest)
    (hflags : checkerFlagManifest)
    (hcompat : transcriptCompatibilityWitness)
    (hrecheck : freshRecheckTranscriptDigest)
    (hinvalidation : invalidationLedger)
    (hbundle : resultBundleDigest)
    (harchive : archiveManifest)
    (hfallback : fallbackRecomputeNoClaimPath)
    (haudit : auditTranscript) :
    ay_cvug_upgrade_contract benchmarkFingerprint artifactDigest
      oldCheckerVersionDigest newCheckerVersionDigest checkerFlagManifest
      transcriptCompatibilityWitness freshRecheckTranscriptDigest
      invalidationLedger resultBundleDigest archiveManifest
      fallbackRecomputeNoClaimPath auditTranscript :=
  fun result k =>
    k hbenchmark hartifact holdchecker hnewchecker hflags hcompat hrecheck
      hinvalidation hbundle harchive hfallback haudit

theorem ay_cvug_contract_benchmark
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (h :
      ay_cvug_upgrade_contract benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest newCheckerVersionDigest checkerFlagManifest
        transcriptCompatibilityWitness freshRecheckTranscriptDigest
        invalidationLedger resultBundleDigest archiveManifest
        fallbackRecomputeNoClaimPath auditTranscript) :
    benchmarkFingerprint :=
  h benchmarkFingerprint (fun hbenchmark _ _ _ _ _ _ _ _ _ _ _ => hbenchmark)

theorem ay_cvug_contract_artifact
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (h :
      ay_cvug_upgrade_contract benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest newCheckerVersionDigest checkerFlagManifest
        transcriptCompatibilityWitness freshRecheckTranscriptDigest
        invalidationLedger resultBundleDigest archiveManifest
        fallbackRecomputeNoClaimPath auditTranscript) :
    artifactDigest :=
  h artifactDigest (fun _ hartifact _ _ _ _ _ _ _ _ _ _ => hartifact)

theorem ay_cvug_contract_old_checker
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (h :
      ay_cvug_upgrade_contract benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest newCheckerVersionDigest checkerFlagManifest
        transcriptCompatibilityWitness freshRecheckTranscriptDigest
        invalidationLedger resultBundleDigest archiveManifest
        fallbackRecomputeNoClaimPath auditTranscript) :
    oldCheckerVersionDigest :=
  h oldCheckerVersionDigest (fun _ _ holdchecker _ _ _ _ _ _ _ _ _ => holdchecker)

theorem ay_cvug_contract_new_checker
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (h :
      ay_cvug_upgrade_contract benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest newCheckerVersionDigest checkerFlagManifest
        transcriptCompatibilityWitness freshRecheckTranscriptDigest
        invalidationLedger resultBundleDigest archiveManifest
        fallbackRecomputeNoClaimPath auditTranscript) :
    newCheckerVersionDigest :=
  h newCheckerVersionDigest (fun _ _ _ hnewchecker _ _ _ _ _ _ _ _ => hnewchecker)

theorem ay_cvug_contract_checker_flags
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (h :
      ay_cvug_upgrade_contract benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest newCheckerVersionDigest checkerFlagManifest
        transcriptCompatibilityWitness freshRecheckTranscriptDigest
        invalidationLedger resultBundleDigest archiveManifest
        fallbackRecomputeNoClaimPath auditTranscript) :
    checkerFlagManifest :=
  h checkerFlagManifest (fun _ _ _ _ hflags _ _ _ _ _ _ _ => hflags)

theorem ay_cvug_contract_compatibility
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (h :
      ay_cvug_upgrade_contract benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest newCheckerVersionDigest checkerFlagManifest
        transcriptCompatibilityWitness freshRecheckTranscriptDigest
        invalidationLedger resultBundleDigest archiveManifest
        fallbackRecomputeNoClaimPath auditTranscript) :
    transcriptCompatibilityWitness :=
  h transcriptCompatibilityWitness (fun _ _ _ _ _ hcompat _ _ _ _ _ _ => hcompat)

theorem ay_cvug_contract_fresh_recheck
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (h :
      ay_cvug_upgrade_contract benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest newCheckerVersionDigest checkerFlagManifest
        transcriptCompatibilityWitness freshRecheckTranscriptDigest
        invalidationLedger resultBundleDigest archiveManifest
        fallbackRecomputeNoClaimPath auditTranscript) :
    freshRecheckTranscriptDigest :=
  h freshRecheckTranscriptDigest (fun _ _ _ _ _ _ hrecheck _ _ _ _ _ => hrecheck)

theorem ay_cvug_contract_invalidation
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (h :
      ay_cvug_upgrade_contract benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest newCheckerVersionDigest checkerFlagManifest
        transcriptCompatibilityWitness freshRecheckTranscriptDigest
        invalidationLedger resultBundleDigest archiveManifest
        fallbackRecomputeNoClaimPath auditTranscript) :
    invalidationLedger :=
  h invalidationLedger (fun _ _ _ _ _ _ _ hinvalidation _ _ _ _ => hinvalidation)

theorem ay_cvug_contract_result_bundle
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (h :
      ay_cvug_upgrade_contract benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest newCheckerVersionDigest checkerFlagManifest
        transcriptCompatibilityWitness freshRecheckTranscriptDigest
        invalidationLedger resultBundleDigest archiveManifest
        fallbackRecomputeNoClaimPath auditTranscript) :
    resultBundleDigest :=
  h resultBundleDigest (fun _ _ _ _ _ _ _ _ hbundle _ _ _ => hbundle)

theorem ay_cvug_contract_archive
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (h :
      ay_cvug_upgrade_contract benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest newCheckerVersionDigest checkerFlagManifest
        transcriptCompatibilityWitness freshRecheckTranscriptDigest
        invalidationLedger resultBundleDigest archiveManifest
        fallbackRecomputeNoClaimPath auditTranscript) :
    archiveManifest :=
  h archiveManifest (fun _ _ _ _ _ _ _ _ _ harchive _ _ => harchive)

theorem ay_cvug_contract_fallback_path
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (h :
      ay_cvug_upgrade_contract benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest newCheckerVersionDigest checkerFlagManifest
        transcriptCompatibilityWitness freshRecheckTranscriptDigest
        invalidationLedger resultBundleDigest archiveManifest
        fallbackRecomputeNoClaimPath auditTranscript) :
    fallbackRecomputeNoClaimPath :=
  h fallbackRecomputeNoClaimPath (fun _ _ _ _ _ _ _ _ _ _ hfallback _ => hfallback)

theorem ay_cvug_contract_audit
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      newCheckerVersionDigest checkerFlagManifest transcriptCompatibilityWitness
      freshRecheckTranscriptDigest invalidationLedger resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (h :
      ay_cvug_upgrade_contract benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest newCheckerVersionDigest checkerFlagManifest
        transcriptCompatibilityWitness freshRecheckTranscriptDigest
        invalidationLedger resultBundleDigest archiveManifest
        fallbackRecomputeNoClaimPath auditTranscript) :
    auditTranscript :=
  h auditTranscript (fun _ _ _ _ _ _ _ _ _ _ _ haudit => haudit)

def ay_cvug_new_checker_evidence
    (compatibilityEvidence freshRecheckEvidence : Prop) : Prop :=
  ay_cvug_disj compatibilityEvidence freshRecheckEvidence

theorem ay_cvug_new_checker_evidence_from_compatibility
    {compatibilityEvidence freshRecheckEvidence : Prop}
    (h : compatibilityEvidence) :
    ay_cvug_new_checker_evidence compatibilityEvidence freshRecheckEvidence :=
  ay_cvug_disj_left h

theorem ay_cvug_new_checker_evidence_from_fresh_recheck
    {compatibilityEvidence freshRecheckEvidence : Prop}
    (h : freshRecheckEvidence) :
    ay_cvug_new_checker_evidence compatibilityEvidence freshRecheckEvidence :=
  ay_cvug_disj_right h

def ay_cvug_upgraded_result
    (upgradeContract newCheckerEvidence checkerBackedArtifact resultKindMatches
      originalBenchmarkClaim : Prop) : Prop :=
  ay_cvug_conj upgradeContract
    (ay_cvug_conj newCheckerEvidence
      (ay_cvug_conj checkerBackedArtifact
        (ay_cvug_conj resultKindMatches originalBenchmarkClaim)))

def ay_cvug_sat_publication
    (upgradeContract newCheckerEvidence checkerBackedArtifact checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_cvug_upgraded_result upgradeContract newCheckerEvidence
    checkerBackedArtifact checkedModel originalBenchmarkSat

def ay_cvug_unsat_publication
    (upgradeContract newCheckerEvidence checkerBackedArtifact checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_cvug_upgraded_result upgradeContract newCheckerEvidence
    checkerBackedArtifact checkedProof originalBenchmarkUnsat

theorem ay_cvug_upgraded_result_intro
    {upgradeContract newCheckerEvidence checkerBackedArtifact resultKindMatches
      originalBenchmarkClaim : Prop}
    (hcontract : upgradeContract)
    (hnewchecker : newCheckerEvidence)
    (hartifact : checkerBackedArtifact)
    (hkind : resultKindMatches)
    (hclaim : originalBenchmarkClaim) :
    ay_cvug_upgraded_result upgradeContract newCheckerEvidence
      checkerBackedArtifact resultKindMatches originalBenchmarkClaim :=
  ay_cvug_conj_intro hcontract
    (ay_cvug_conj_intro hnewchecker
      (ay_cvug_conj_intro hartifact (ay_cvug_conj_intro hkind hclaim)))

theorem ay_cvug_sat_publication_intro
    {upgradeContract newCheckerEvidence checkerBackedArtifact checkedModel
      originalBenchmarkSat : Prop}
    (hcontract : upgradeContract)
    (hnewchecker : newCheckerEvidence)
    (hartifact : checkerBackedArtifact)
    (hmodel : checkedModel)
    (hsat : originalBenchmarkSat) :
    ay_cvug_sat_publication upgradeContract newCheckerEvidence
      checkerBackedArtifact checkedModel originalBenchmarkSat :=
  ay_cvug_upgraded_result_intro hcontract hnewchecker hartifact hmodel hsat

theorem ay_cvug_unsat_publication_intro
    {upgradeContract newCheckerEvidence checkerBackedArtifact checkedProof
      originalBenchmarkUnsat : Prop}
    (hcontract : upgradeContract)
    (hnewchecker : newCheckerEvidence)
    (hartifact : checkerBackedArtifact)
    (hproof : checkedProof)
    (hunsat : originalBenchmarkUnsat) :
    ay_cvug_unsat_publication upgradeContract newCheckerEvidence
      checkerBackedArtifact checkedProof originalBenchmarkUnsat :=
  ay_cvug_upgraded_result_intro hcontract hnewchecker hartifact hproof hunsat

theorem ay_cvug_result_requires_upgrade_contract
    {upgradeContract newCheckerEvidence checkerBackedArtifact resultKindMatches
      originalBenchmarkClaim : Prop}
    (h :
      ay_cvug_upgraded_result upgradeContract newCheckerEvidence
        checkerBackedArtifact resultKindMatches originalBenchmarkClaim) :
    upgradeContract :=
  ay_cvug_conj_left h

theorem ay_cvug_result_requires_new_checker_evidence
    {upgradeContract newCheckerEvidence checkerBackedArtifact resultKindMatches
      originalBenchmarkClaim : Prop}
    (h :
      ay_cvug_upgraded_result upgradeContract newCheckerEvidence
        checkerBackedArtifact resultKindMatches originalBenchmarkClaim) :
    newCheckerEvidence :=
  ay_cvug_conj_left (ay_cvug_conj_right h)

theorem ay_cvug_result_requires_checker_backed_artifact
    {upgradeContract newCheckerEvidence checkerBackedArtifact resultKindMatches
      originalBenchmarkClaim : Prop}
    (h :
      ay_cvug_upgraded_result upgradeContract newCheckerEvidence
        checkerBackedArtifact resultKindMatches originalBenchmarkClaim) :
    checkerBackedArtifact :=
  ay_cvug_conj_left (ay_cvug_conj_right (ay_cvug_conj_right h))

theorem ay_cvug_result_kind_matches
    {upgradeContract newCheckerEvidence checkerBackedArtifact resultKindMatches
      originalBenchmarkClaim : Prop}
    (h :
      ay_cvug_upgraded_result upgradeContract newCheckerEvidence
        checkerBackedArtifact resultKindMatches originalBenchmarkClaim) :
    resultKindMatches :=
  ay_cvug_conj_left
    (ay_cvug_conj_right (ay_cvug_conj_right (ay_cvug_conj_right h)))

theorem ay_cvug_result_original_claim
    {upgradeContract newCheckerEvidence checkerBackedArtifact resultKindMatches
      originalBenchmarkClaim : Prop}
    (h :
      ay_cvug_upgraded_result upgradeContract newCheckerEvidence
        checkerBackedArtifact resultKindMatches originalBenchmarkClaim) :
    originalBenchmarkClaim :=
  ay_cvug_conj_right
    (ay_cvug_conj_right (ay_cvug_conj_right (ay_cvug_conj_right h)))

theorem ay_cvug_accepted_upgrade_requires_compat_or_fresh_recheck
    {upgradeContract newCheckerEvidence checkerBackedArtifact resultKindMatches
      originalBenchmarkClaim : Prop}
    (h :
      ay_cvug_upgraded_result upgradeContract newCheckerEvidence
        checkerBackedArtifact resultKindMatches originalBenchmarkClaim) :
    newCheckerEvidence :=
  ay_cvug_result_requires_new_checker_evidence h

theorem ay_cvug_accepted_sat_preserves_soundness
    {upgradeContract newCheckerEvidence checkerBackedArtifact checkedModel
      originalBenchmarkSat : Prop}
    (h :
      ay_cvug_sat_publication upgradeContract newCheckerEvidence
        checkerBackedArtifact checkedModel originalBenchmarkSat) :
    originalBenchmarkSat :=
  ay_cvug_result_original_claim h

theorem ay_cvug_accepted_unsat_preserves_soundness
    {upgradeContract newCheckerEvidence checkerBackedArtifact checkedProof
      originalBenchmarkUnsat : Prop}
    (h :
      ay_cvug_unsat_publication upgradeContract newCheckerEvidence
        checkerBackedArtifact checkedProof originalBenchmarkUnsat) :
    originalBenchmarkUnsat :=
  ay_cvug_result_original_claim h

def ay_cvug_no_claim (diagnostic recompute auditTranscript : Prop) : Prop :=
  ay_cvug_conj diagnostic (ay_cvug_conj recompute auditTranscript)

theorem ay_cvug_no_claim_intro
    {diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : diagnostic)
    (hrecompute : recompute)
    (haudit : auditTranscript) :
    ay_cvug_no_claim diagnostic recompute auditTranscript :=
  ay_cvug_conj_intro hdiagnostic (ay_cvug_conj_intro hrecompute haudit)

theorem ay_cvug_no_claim_diagnostic
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_cvug_no_claim diagnostic recompute auditTranscript) :
    diagnostic :=
  ay_cvug_conj_left h

theorem ay_cvug_no_claim_recompute
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_cvug_no_claim diagnostic recompute auditTranscript) :
    recompute :=
  ay_cvug_conj_left (ay_cvug_conj_right h)

theorem ay_cvug_no_claim_audit
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_cvug_no_claim diagnostic recompute auditTranscript) :
    auditTranscript :=
  ay_cvug_conj_right (ay_cvug_conj_right h)

def ay_cvug_mismatch_forces_no_claim
    (mismatch diagnostic recompute auditTranscript : Prop) : Prop :=
  mismatch -> ay_cvug_no_claim diagnostic recompute auditTranscript

theorem ay_cvug_mismatch_forces_no_claim_intro
    {mismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : mismatch -> diagnostic)
    (hrecompute : mismatch -> recompute)
    (haudit : mismatch -> auditTranscript) :
    ay_cvug_mismatch_forces_no_claim mismatch diagnostic recompute
      auditTranscript :=
  fun hmismatch =>
    ay_cvug_no_claim_intro (hdiagnostic hmismatch) (hrecompute hmismatch)
      (haudit hmismatch)

theorem ay_cvug_checker_mismatch_forces_no_claim
    {checkerMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : checkerMismatch -> diagnostic)
    (hrecompute : checkerMismatch -> recompute)
    (haudit : checkerMismatch -> auditTranscript) :
    ay_cvug_mismatch_forces_no_claim checkerMismatch diagnostic recompute
      auditTranscript :=
  ay_cvug_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_cvug_version_mismatch_forces_no_claim
    {versionMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : versionMismatch -> diagnostic)
    (hrecompute : versionMismatch -> recompute)
    (haudit : versionMismatch -> auditTranscript) :
    ay_cvug_mismatch_forces_no_claim versionMismatch diagnostic recompute
      auditTranscript :=
  ay_cvug_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_cvug_flag_mismatch_forces_no_claim
    {flagMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : flagMismatch -> diagnostic)
    (hrecompute : flagMismatch -> recompute)
    (haudit : flagMismatch -> auditTranscript) :
    ay_cvug_mismatch_forces_no_claim flagMismatch diagnostic recompute
      auditTranscript :=
  ay_cvug_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_cvug_artifact_mismatch_forces_no_claim
    {artifactMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : artifactMismatch -> diagnostic)
    (hrecompute : artifactMismatch -> recompute)
    (haudit : artifactMismatch -> auditTranscript) :
    ay_cvug_mismatch_forces_no_claim artifactMismatch diagnostic recompute
      auditTranscript :=
  ay_cvug_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_cvug_transcript_mismatch_forces_no_claim
    {transcriptMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : transcriptMismatch -> diagnostic)
    (hrecompute : transcriptMismatch -> recompute)
    (haudit : transcriptMismatch -> auditTranscript) :
    ay_cvug_mismatch_forces_no_claim transcriptMismatch diagnostic recompute
      auditTranscript :=
  ay_cvug_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_cvug_invalidation_mismatch_forces_no_claim
    {invalidationMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : invalidationMismatch -> diagnostic)
    (hrecompute : invalidationMismatch -> recompute)
    (haudit : invalidationMismatch -> auditTranscript) :
    ay_cvug_mismatch_forces_no_claim invalidationMismatch diagnostic recompute
      auditTranscript :=
  ay_cvug_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_cvug_bundle_mismatch_forces_no_claim
    {bundleMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : bundleMismatch -> diagnostic)
    (hrecompute : bundleMismatch -> recompute)
    (haudit : bundleMismatch -> auditTranscript) :
    ay_cvug_mismatch_forces_no_claim bundleMismatch diagnostic recompute
      auditTranscript :=
  ay_cvug_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_cvug_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : archiveMismatch -> diagnostic)
    (hrecompute : archiveMismatch -> recompute)
    (haudit : archiveMismatch -> auditTranscript) :
    ay_cvug_mismatch_forces_no_claim archiveMismatch diagnostic recompute
      auditTranscript :=
  ay_cvug_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_cvug_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : auditMismatch -> diagnostic)
    (hrecompute : auditMismatch -> recompute)
    (haudit : auditMismatch -> auditTranscript) :
    ay_cvug_mismatch_forces_no_claim auditMismatch diagnostic recompute
      auditTranscript :=
  ay_cvug_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

def ay_cvug_old_checker_transcript_only
    (benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      checkerFlagManifest resultBundleDigest archiveManifest
      fallbackRecomputeNoClaimPath auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkFingerprint ->
      artifactDigest ->
      oldCheckerVersionDigest ->
      checkerFlagManifest ->
      resultBundleDigest ->
      archiveManifest ->
      fallbackRecomputeNoClaimPath ->
      auditTranscript ->
      result) ->
    result

theorem ay_cvug_old_checker_transcript_only_intro
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      checkerFlagManifest resultBundleDigest archiveManifest
      fallbackRecomputeNoClaimPath auditTranscript : Prop}
    (hbenchmark : benchmarkFingerprint)
    (hartifact : artifactDigest)
    (holdchecker : oldCheckerVersionDigest)
    (hflags : checkerFlagManifest)
    (hbundle : resultBundleDigest)
    (harchive : archiveManifest)
    (hfallback : fallbackRecomputeNoClaimPath)
    (haudit : auditTranscript) :
    ay_cvug_old_checker_transcript_only benchmarkFingerprint artifactDigest
      oldCheckerVersionDigest checkerFlagManifest resultBundleDigest
      archiveManifest fallbackRecomputeNoClaimPath auditTranscript :=
  fun result k =>
    k hbenchmark hartifact holdchecker hflags hbundle harchive hfallback haudit

def ay_cvug_blocks_sat (noClaim publicSat : Prop) : Prop :=
  publicSat -> noClaim

def ay_cvug_blocks_unsat (noClaim publicUnsat : Prop) : Prop :=
  publicUnsat -> noClaim

theorem ay_cvug_stale_old_checker_transcript_alone_cannot_publish_sat
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      checkerFlagManifest resultBundleDigest archiveManifest
      fallbackRecomputeNoClaimPath auditTranscript noClaim publicSat : Prop}
    (h :
      ay_cvug_old_checker_transcript_only benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest checkerFlagManifest resultBundleDigest
        archiveManifest fallbackRecomputeNoClaimPath auditTranscript)
    (hnoClaim : fallbackRecomputeNoClaimPath -> noClaim) :
    ay_cvug_blocks_sat noClaim publicSat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

theorem ay_cvug_stale_old_checker_transcript_alone_cannot_publish_unsat
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      checkerFlagManifest resultBundleDigest archiveManifest
      fallbackRecomputeNoClaimPath auditTranscript noClaim publicUnsat : Prop}
    (h :
      ay_cvug_old_checker_transcript_only benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest checkerFlagManifest resultBundleDigest
        archiveManifest fallbackRecomputeNoClaimPath auditTranscript)
    (hnoClaim : fallbackRecomputeNoClaimPath -> noClaim) :
    ay_cvug_blocks_unsat noClaim publicUnsat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

theorem ay_cvug_old_checker_only_lacks_new_checker_evidence
    {benchmarkFingerprint artifactDigest oldCheckerVersionDigest
      checkerFlagManifest resultBundleDigest archiveManifest
      fallbackRecomputeNoClaimPath auditTranscript newCheckerEvidence noClaim
      : Prop}
    (h :
      ay_cvug_old_checker_transcript_only benchmarkFingerprint artifactDigest
        oldCheckerVersionDigest checkerFlagManifest resultBundleDigest
        archiveManifest fallbackRecomputeNoClaimPath auditTranscript)
    (hnoClaim : fallbackRecomputeNoClaimPath -> noClaim) :
    newCheckerEvidence -> noClaim :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

def ay_cvug_failed_guard
    (mismatch quarantine recompute noClaim auditTranscript : Prop) : Prop :=
  ay_cvug_conj mismatch
    (ay_cvug_conj quarantine
      (ay_cvug_conj recompute (ay_cvug_conj noClaim auditTranscript)))

theorem ay_cvug_failed_guard_intro
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (hmismatch : mismatch)
    (hquarantine : quarantine)
    (hrecompute : recompute)
    (hnoclaim : noClaim)
    (haudit : auditTranscript) :
    ay_cvug_failed_guard mismatch quarantine recompute noClaim auditTranscript :=
  ay_cvug_conj_intro hmismatch
    (ay_cvug_conj_intro hquarantine
      (ay_cvug_conj_intro hrecompute (ay_cvug_conj_intro hnoclaim haudit)))

theorem ay_cvug_failed_guard_mismatch
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_cvug_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    mismatch :=
  ay_cvug_conj_left h

theorem ay_cvug_failed_guard_recompute
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_cvug_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    recompute :=
  ay_cvug_conj_left (ay_cvug_conj_right (ay_cvug_conj_right h))

theorem ay_cvug_failed_guard_no_claim
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_cvug_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    noClaim :=
  ay_cvug_conj_left
    (ay_cvug_conj_right (ay_cvug_conj_right (ay_cvug_conj_right h)))

theorem ay_cvug_failed_guard_audit
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_cvug_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    auditTranscript :=
  ay_cvug_conj_right
    (ay_cvug_conj_right (ay_cvug_conj_right (ay_cvug_conj_right h)))

theorem ay_cvug_failed_checker_upgrade_guard_cannot_bless_sat
    {mismatch quarantine recompute noClaim auditTranscript publicSat : Prop}
    (h : ay_cvug_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    ay_cvug_blocks_sat noClaim publicSat :=
  fun _ => ay_cvug_failed_guard_no_claim h

theorem ay_cvug_failed_checker_upgrade_guard_cannot_bless_unsat
    {mismatch quarantine recompute noClaim auditTranscript publicUnsat : Prop}
    (h : ay_cvug_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    ay_cvug_blocks_unsat noClaim publicUnsat :=
  fun _ => ay_cvug_failed_guard_no_claim h

theorem ay_cvug_failed_guard_forces_recompute
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_cvug_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    recompute :=
  ay_cvug_failed_guard_recompute h
