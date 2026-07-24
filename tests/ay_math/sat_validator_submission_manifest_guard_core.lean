-- SAT-COMP submission manifest guard for sequential-main validation.
-- Self-contained propositional contract for coherent ay submission bundles.

def ay_smg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_smg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

theorem ay_smg_conj_intro {left right : Prop} (hleft : left) (hright : right) :
    ay_smg_conj left right :=
  fun result k => k hleft hright

theorem ay_smg_conj_left {left right : Prop} (h : ay_smg_conj left right) :
    left :=
  h left (fun hleft _ => hleft)

theorem ay_smg_conj_right {left right : Prop} (h : ay_smg_conj left right) :
    right :=
  h right (fun _ hright => hright)

theorem ay_smg_disj_left {left right : Prop} (hleft : left) :
    ay_smg_disj left right :=
  fun result kleft _ => kleft hleft

theorem ay_smg_disj_right {left right : Prop} (hright : right) :
    ay_smg_disj left right :=
  fun result _ kright => kright hright

def ay_smg_submission_contract
    (solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      validationTranscriptDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (solverBinaryDigest ->
      sourceBuildDigest ->
      configurationManifest ->
      benchmarkListDigest ->
      perBenchmarkResultBundleDigests ->
      checkerVersionDigest ->
      validationTranscriptDigest ->
      resourceLimitManifest ->
      archiveUploadManifest ->
      noClaimFallbackLedger ->
      auditTranscript ->
      result) ->
    result

theorem ay_smg_submission_contract_intro
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      validationTranscriptDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript : Prop}
    (hbinary : solverBinaryDigest)
    (hsource : sourceBuildDigest)
    (hconfig : configurationManifest)
    (hbenchmarks : benchmarkListDigest)
    (hbundles : perBenchmarkResultBundleDigests)
    (hchecker : checkerVersionDigest)
    (hvalidation : validationTranscriptDigest)
    (hresource : resourceLimitManifest)
    (harchive : archiveUploadManifest)
    (hfallback : noClaimFallbackLedger)
    (haudit : auditTranscript) :
    ay_smg_submission_contract solverBinaryDigest sourceBuildDigest
      configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
      checkerVersionDigest validationTranscriptDigest resourceLimitManifest
      archiveUploadManifest noClaimFallbackLedger auditTranscript :=
  fun result k =>
    k hbinary hsource hconfig hbenchmarks hbundles hchecker hvalidation
      hresource harchive hfallback haudit

theorem ay_smg_contract_binary
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      validationTranscriptDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript : Prop}
    (h :
      ay_smg_submission_contract solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest validationTranscriptDigest resourceLimitManifest
        archiveUploadManifest noClaimFallbackLedger auditTranscript) :
    solverBinaryDigest :=
  h solverBinaryDigest (fun hbinary _ _ _ _ _ _ _ _ _ _ => hbinary)

theorem ay_smg_contract_source_build
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      validationTranscriptDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript : Prop}
    (h :
      ay_smg_submission_contract solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest validationTranscriptDigest resourceLimitManifest
        archiveUploadManifest noClaimFallbackLedger auditTranscript) :
    sourceBuildDigest :=
  h sourceBuildDigest (fun _ hsource _ _ _ _ _ _ _ _ _ => hsource)

theorem ay_smg_contract_configuration
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      validationTranscriptDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript : Prop}
    (h :
      ay_smg_submission_contract solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest validationTranscriptDigest resourceLimitManifest
        archiveUploadManifest noClaimFallbackLedger auditTranscript) :
    configurationManifest :=
  h configurationManifest (fun _ _ hconfig _ _ _ _ _ _ _ _ => hconfig)

theorem ay_smg_contract_benchmark_list
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      validationTranscriptDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript : Prop}
    (h :
      ay_smg_submission_contract solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest validationTranscriptDigest resourceLimitManifest
        archiveUploadManifest noClaimFallbackLedger auditTranscript) :
    benchmarkListDigest :=
  h benchmarkListDigest (fun _ _ _ hbenchmarks _ _ _ _ _ _ _ => hbenchmarks)

theorem ay_smg_contract_result_bundles
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      validationTranscriptDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript : Prop}
    (h :
      ay_smg_submission_contract solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest validationTranscriptDigest resourceLimitManifest
        archiveUploadManifest noClaimFallbackLedger auditTranscript) :
    perBenchmarkResultBundleDigests :=
  h perBenchmarkResultBundleDigests
    (fun _ _ _ _ hbundles _ _ _ _ _ _ => hbundles)

theorem ay_smg_contract_checker_version
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      validationTranscriptDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript : Prop}
    (h :
      ay_smg_submission_contract solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest validationTranscriptDigest resourceLimitManifest
        archiveUploadManifest noClaimFallbackLedger auditTranscript) :
    checkerVersionDigest :=
  h checkerVersionDigest (fun _ _ _ _ _ hchecker _ _ _ _ _ => hchecker)

theorem ay_smg_contract_validation_transcript
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      validationTranscriptDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript : Prop}
    (h :
      ay_smg_submission_contract solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest validationTranscriptDigest resourceLimitManifest
        archiveUploadManifest noClaimFallbackLedger auditTranscript) :
    validationTranscriptDigest :=
  h validationTranscriptDigest
    (fun _ _ _ _ _ _ hvalidation _ _ _ _ => hvalidation)

theorem ay_smg_contract_resource_limit
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      validationTranscriptDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript : Prop}
    (h :
      ay_smg_submission_contract solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest validationTranscriptDigest resourceLimitManifest
        archiveUploadManifest noClaimFallbackLedger auditTranscript) :
    resourceLimitManifest :=
  h resourceLimitManifest (fun _ _ _ _ _ _ _ hresource _ _ _ => hresource)

theorem ay_smg_contract_archive_upload
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      validationTranscriptDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript : Prop}
    (h :
      ay_smg_submission_contract solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest validationTranscriptDigest resourceLimitManifest
        archiveUploadManifest noClaimFallbackLedger auditTranscript) :
    archiveUploadManifest :=
  h archiveUploadManifest (fun _ _ _ _ _ _ _ _ harchive _ _ => harchive)

theorem ay_smg_contract_fallback_ledger
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      validationTranscriptDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript : Prop}
    (h :
      ay_smg_submission_contract solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest validationTranscriptDigest resourceLimitManifest
        archiveUploadManifest noClaimFallbackLedger auditTranscript) :
    noClaimFallbackLedger :=
  h noClaimFallbackLedger (fun _ _ _ _ _ _ _ _ _ hfallback _ => hfallback)

theorem ay_smg_contract_audit
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      validationTranscriptDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript : Prop}
    (h :
      ay_smg_submission_contract solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest validationTranscriptDigest resourceLimitManifest
        archiveUploadManifest noClaimFallbackLedger auditTranscript) :
    auditTranscript :=
  h auditTranscript (fun _ _ _ _ _ _ _ _ _ _ haudit => haudit)

def ay_smg_checked_entry
    (submissionContract coherentBundle checkerBackedEvidence resultKindMatches
      originalBenchmarkClaim : Prop) : Prop :=
  ay_smg_conj submissionContract
    (ay_smg_conj coherentBundle
      (ay_smg_conj checkerBackedEvidence
        (ay_smg_conj resultKindMatches originalBenchmarkClaim)))

def ay_smg_sat_publication
    (submissionContract coherentBundle checkerBackedEvidence checkedModel
      originalBenchmarkSat : Prop) : Prop :=
  ay_smg_checked_entry submissionContract coherentBundle checkerBackedEvidence
    checkedModel originalBenchmarkSat

def ay_smg_unsat_publication
    (submissionContract coherentBundle checkerBackedEvidence checkedProof
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_smg_checked_entry submissionContract coherentBundle checkerBackedEvidence
    checkedProof originalBenchmarkUnsat

theorem ay_smg_checked_entry_intro
    {submissionContract coherentBundle checkerBackedEvidence resultKindMatches
      originalBenchmarkClaim : Prop}
    (hcontract : submissionContract)
    (hbundle : coherentBundle)
    (hchecker : checkerBackedEvidence)
    (hkind : resultKindMatches)
    (hclaim : originalBenchmarkClaim) :
    ay_smg_checked_entry submissionContract coherentBundle checkerBackedEvidence
      resultKindMatches originalBenchmarkClaim :=
  ay_smg_conj_intro hcontract
    (ay_smg_conj_intro hbundle
      (ay_smg_conj_intro hchecker (ay_smg_conj_intro hkind hclaim)))

theorem ay_smg_sat_publication_intro
    {submissionContract coherentBundle checkerBackedEvidence checkedModel
      originalBenchmarkSat : Prop}
    (hcontract : submissionContract)
    (hbundle : coherentBundle)
    (hchecker : checkerBackedEvidence)
    (hmodel : checkedModel)
    (hsat : originalBenchmarkSat) :
    ay_smg_sat_publication submissionContract coherentBundle
      checkerBackedEvidence checkedModel originalBenchmarkSat :=
  ay_smg_checked_entry_intro hcontract hbundle hchecker hmodel hsat

theorem ay_smg_unsat_publication_intro
    {submissionContract coherentBundle checkerBackedEvidence checkedProof
      originalBenchmarkUnsat : Prop}
    (hcontract : submissionContract)
    (hbundle : coherentBundle)
    (hchecker : checkerBackedEvidence)
    (hproof : checkedProof)
    (hunsat : originalBenchmarkUnsat) :
    ay_smg_unsat_publication submissionContract coherentBundle
      checkerBackedEvidence checkedProof originalBenchmarkUnsat :=
  ay_smg_checked_entry_intro hcontract hbundle hchecker hproof hunsat

theorem ay_smg_checked_entry_contract
    {submissionContract coherentBundle checkerBackedEvidence resultKindMatches
      originalBenchmarkClaim : Prop}
    (h :
      ay_smg_checked_entry submissionContract coherentBundle checkerBackedEvidence
        resultKindMatches originalBenchmarkClaim) :
    submissionContract :=
  ay_smg_conj_left h

theorem ay_smg_checked_entry_bundle
    {submissionContract coherentBundle checkerBackedEvidence resultKindMatches
      originalBenchmarkClaim : Prop}
    (h :
      ay_smg_checked_entry submissionContract coherentBundle checkerBackedEvidence
        resultKindMatches originalBenchmarkClaim) :
    coherentBundle :=
  ay_smg_conj_left (ay_smg_conj_right h)

theorem ay_smg_checked_entry_checker_backed
    {submissionContract coherentBundle checkerBackedEvidence resultKindMatches
      originalBenchmarkClaim : Prop}
    (h :
      ay_smg_checked_entry submissionContract coherentBundle checkerBackedEvidence
        resultKindMatches originalBenchmarkClaim) :
    checkerBackedEvidence :=
  ay_smg_conj_left (ay_smg_conj_right (ay_smg_conj_right h))

theorem ay_smg_checked_entry_result_kind
    {submissionContract coherentBundle checkerBackedEvidence resultKindMatches
      originalBenchmarkClaim : Prop}
    (h :
      ay_smg_checked_entry submissionContract coherentBundle checkerBackedEvidence
        resultKindMatches originalBenchmarkClaim) :
    resultKindMatches :=
  ay_smg_conj_left
    (ay_smg_conj_right (ay_smg_conj_right (ay_smg_conj_right h)))

theorem ay_smg_checked_entry_claim
    {submissionContract coherentBundle checkerBackedEvidence resultKindMatches
      originalBenchmarkClaim : Prop}
    (h :
      ay_smg_checked_entry submissionContract coherentBundle checkerBackedEvidence
        resultKindMatches originalBenchmarkClaim) :
    originalBenchmarkClaim :=
  ay_smg_conj_right
    (ay_smg_conj_right (ay_smg_conj_right (ay_smg_conj_right h)))

theorem ay_smg_accepted_entry_tied_to_coherent_bundle
    {submissionContract coherentBundle checkerBackedEvidence resultKindMatches
      originalBenchmarkClaim : Prop}
    (h :
      ay_smg_checked_entry submissionContract coherentBundle checkerBackedEvidence
        resultKindMatches originalBenchmarkClaim) :
    coherentBundle :=
  ay_smg_checked_entry_bundle h

theorem ay_smg_accepted_entry_has_checker_backed_evidence
    {submissionContract coherentBundle checkerBackedEvidence resultKindMatches
      originalBenchmarkClaim : Prop}
    (h :
      ay_smg_checked_entry submissionContract coherentBundle checkerBackedEvidence
        resultKindMatches originalBenchmarkClaim) :
    checkerBackedEvidence :=
  ay_smg_checked_entry_checker_backed h

theorem ay_smg_accepted_sat_preserves_soundness
    {submissionContract coherentBundle checkerBackedEvidence checkedModel
      originalBenchmarkSat : Prop}
    (h :
      ay_smg_sat_publication submissionContract coherentBundle
        checkerBackedEvidence checkedModel originalBenchmarkSat) :
    originalBenchmarkSat :=
  ay_smg_checked_entry_claim h

theorem ay_smg_accepted_unsat_preserves_soundness
    {submissionContract coherentBundle checkerBackedEvidence checkedProof
      originalBenchmarkUnsat : Prop}
    (h :
      ay_smg_unsat_publication submissionContract coherentBundle
        checkerBackedEvidence checkedProof originalBenchmarkUnsat) :
    originalBenchmarkUnsat :=
  ay_smg_checked_entry_claim h

def ay_smg_no_claim (diagnostic recompute auditTranscript : Prop) : Prop :=
  ay_smg_conj diagnostic (ay_smg_conj recompute auditTranscript)

theorem ay_smg_no_claim_intro
    {diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : diagnostic)
    (hrecompute : recompute)
    (haudit : auditTranscript) :
    ay_smg_no_claim diagnostic recompute auditTranscript :=
  ay_smg_conj_intro hdiagnostic (ay_smg_conj_intro hrecompute haudit)

theorem ay_smg_no_claim_diagnostic
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_smg_no_claim diagnostic recompute auditTranscript) :
    diagnostic :=
  ay_smg_conj_left h

theorem ay_smg_no_claim_recompute
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_smg_no_claim diagnostic recompute auditTranscript) :
    recompute :=
  ay_smg_conj_left (ay_smg_conj_right h)

theorem ay_smg_no_claim_audit
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_smg_no_claim diagnostic recompute auditTranscript) :
    auditTranscript :=
  ay_smg_conj_right (ay_smg_conj_right h)

def ay_smg_mismatch_forces_no_claim
    (mismatch diagnostic recompute auditTranscript : Prop) : Prop :=
  mismatch -> ay_smg_no_claim diagnostic recompute auditTranscript

theorem ay_smg_mismatch_forces_no_claim_intro
    {mismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : mismatch -> diagnostic)
    (hrecompute : mismatch -> recompute)
    (haudit : mismatch -> auditTranscript) :
    ay_smg_mismatch_forces_no_claim mismatch diagnostic recompute
      auditTranscript :=
  fun hmismatch =>
    ay_smg_no_claim_intro (hdiagnostic hmismatch) (hrecompute hmismatch)
      (haudit hmismatch)

theorem ay_smg_manifest_mismatch_forces_no_claim
    {manifestMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : manifestMismatch -> diagnostic)
    (hrecompute : manifestMismatch -> recompute)
    (haudit : manifestMismatch -> auditTranscript) :
    ay_smg_mismatch_forces_no_claim manifestMismatch diagnostic recompute
      auditTranscript :=
  ay_smg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_smg_binary_mismatch_forces_no_claim
    {binaryMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : binaryMismatch -> diagnostic)
    (hrecompute : binaryMismatch -> recompute)
    (haudit : binaryMismatch -> auditTranscript) :
    ay_smg_mismatch_forces_no_claim binaryMismatch diagnostic recompute
      auditTranscript :=
  ay_smg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_smg_source_mismatch_forces_no_claim
    {sourceMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : sourceMismatch -> diagnostic)
    (hrecompute : sourceMismatch -> recompute)
    (haudit : sourceMismatch -> auditTranscript) :
    ay_smg_mismatch_forces_no_claim sourceMismatch diagnostic recompute
      auditTranscript :=
  ay_smg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_smg_config_mismatch_forces_no_claim
    {configMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : configMismatch -> diagnostic)
    (hrecompute : configMismatch -> recompute)
    (haudit : configMismatch -> auditTranscript) :
    ay_smg_mismatch_forces_no_claim configMismatch diagnostic recompute
      auditTranscript :=
  ay_smg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_smg_benchmark_mismatch_forces_no_claim
    {benchmarkMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : benchmarkMismatch -> diagnostic)
    (hrecompute : benchmarkMismatch -> recompute)
    (haudit : benchmarkMismatch -> auditTranscript) :
    ay_smg_mismatch_forces_no_claim benchmarkMismatch diagnostic recompute
      auditTranscript :=
  ay_smg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_smg_result_mismatch_forces_no_claim
    {resultMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : resultMismatch -> diagnostic)
    (hrecompute : resultMismatch -> recompute)
    (haudit : resultMismatch -> auditTranscript) :
    ay_smg_mismatch_forces_no_claim resultMismatch diagnostic recompute
      auditTranscript :=
  ay_smg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_smg_checker_mismatch_forces_no_claim
    {checkerMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : checkerMismatch -> diagnostic)
    (hrecompute : checkerMismatch -> recompute)
    (haudit : checkerMismatch -> auditTranscript) :
    ay_smg_mismatch_forces_no_claim checkerMismatch diagnostic recompute
      auditTranscript :=
  ay_smg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_smg_resource_mismatch_forces_no_claim
    {resourceMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : resourceMismatch -> diagnostic)
    (hrecompute : resourceMismatch -> recompute)
    (haudit : resourceMismatch -> auditTranscript) :
    ay_smg_mismatch_forces_no_claim resourceMismatch diagnostic recompute
      auditTranscript :=
  ay_smg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_smg_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : archiveMismatch -> diagnostic)
    (hrecompute : archiveMismatch -> recompute)
    (haudit : archiveMismatch -> auditTranscript) :
    ay_smg_mismatch_forces_no_claim archiveMismatch diagnostic recompute
      auditTranscript :=
  ay_smg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_smg_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : auditMismatch -> diagnostic)
    (hrecompute : auditMismatch -> recompute)
    (haudit : auditMismatch -> auditTranscript) :
    ay_smg_mismatch_forces_no_claim auditMismatch diagnostic recompute
      auditTranscript :=
  ay_smg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

def ay_smg_submission_manifest_only
    (solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      resourceLimitManifest archiveUploadManifest noClaimFallbackLedger
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (solverBinaryDigest ->
      sourceBuildDigest ->
      configurationManifest ->
      benchmarkListDigest ->
      perBenchmarkResultBundleDigests ->
      checkerVersionDigest ->
      resourceLimitManifest ->
      archiveUploadManifest ->
      noClaimFallbackLedger ->
      auditTranscript ->
      result) ->
    result

theorem ay_smg_submission_manifest_only_intro
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      resourceLimitManifest archiveUploadManifest noClaimFallbackLedger
      auditTranscript : Prop}
    (hbinary : solverBinaryDigest)
    (hsource : sourceBuildDigest)
    (hconfig : configurationManifest)
    (hbenchmarks : benchmarkListDigest)
    (hbundles : perBenchmarkResultBundleDigests)
    (hchecker : checkerVersionDigest)
    (hresource : resourceLimitManifest)
    (harchive : archiveUploadManifest)
    (hfallback : noClaimFallbackLedger)
    (haudit : auditTranscript) :
    ay_smg_submission_manifest_only solverBinaryDigest sourceBuildDigest
      configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
      checkerVersionDigest resourceLimitManifest archiveUploadManifest
      noClaimFallbackLedger auditTranscript :=
  fun result k =>
    k hbinary hsource hconfig hbenchmarks hbundles hchecker hresource
      harchive hfallback haudit

def ay_smg_blocks_sat (noClaim publicSat : Prop) : Prop :=
  publicSat -> noClaim

def ay_smg_blocks_unsat (noClaim publicUnsat : Prop) : Prop :=
  publicUnsat -> noClaim

theorem ay_smg_submission_manifest_alone_cannot_publish_sat
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      resourceLimitManifest archiveUploadManifest noClaimFallbackLedger
      auditTranscript noClaim publicSat : Prop}
    (h :
      ay_smg_submission_manifest_only solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest resourceLimitManifest archiveUploadManifest
        noClaimFallbackLedger auditTranscript)
    (hnoClaim : noClaimFallbackLedger -> noClaim) :
    ay_smg_blocks_sat noClaim publicSat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

theorem ay_smg_submission_manifest_alone_cannot_publish_unsat
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      resourceLimitManifest archiveUploadManifest noClaimFallbackLedger
      auditTranscript noClaim publicUnsat : Prop}
    (h :
      ay_smg_submission_manifest_only solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest resourceLimitManifest archiveUploadManifest
        noClaimFallbackLedger auditTranscript)
    (hnoClaim : noClaimFallbackLedger -> noClaim) :
    ay_smg_blocks_unsat noClaim publicUnsat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

theorem ay_smg_manifest_only_lacks_per_benchmark_checker_evidence
    {solverBinaryDigest sourceBuildDigest configurationManifest
      benchmarkListDigest perBenchmarkResultBundleDigests checkerVersionDigest
      resourceLimitManifest archiveUploadManifest noClaimFallbackLedger
      auditTranscript checkerBackedEvidence noClaim : Prop}
    (h :
      ay_smg_submission_manifest_only solverBinaryDigest sourceBuildDigest
        configurationManifest benchmarkListDigest perBenchmarkResultBundleDigests
        checkerVersionDigest resourceLimitManifest archiveUploadManifest
        noClaimFallbackLedger auditTranscript)
    (hnoClaim : noClaimFallbackLedger -> noClaim) :
    checkerBackedEvidence -> noClaim :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

def ay_smg_failed_guard
    (mismatch quarantine recompute noClaim auditTranscript : Prop) : Prop :=
  ay_smg_conj mismatch
    (ay_smg_conj quarantine
      (ay_smg_conj recompute (ay_smg_conj noClaim auditTranscript)))

theorem ay_smg_failed_guard_intro
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (hmismatch : mismatch)
    (hquarantine : quarantine)
    (hrecompute : recompute)
    (hnoclaim : noClaim)
    (haudit : auditTranscript) :
    ay_smg_failed_guard mismatch quarantine recompute noClaim auditTranscript :=
  ay_smg_conj_intro hmismatch
    (ay_smg_conj_intro hquarantine
      (ay_smg_conj_intro hrecompute (ay_smg_conj_intro hnoclaim haudit)))

theorem ay_smg_failed_guard_mismatch
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_smg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    mismatch :=
  ay_smg_conj_left h

theorem ay_smg_failed_guard_recompute
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_smg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    recompute :=
  ay_smg_conj_left (ay_smg_conj_right (ay_smg_conj_right h))

theorem ay_smg_failed_guard_no_claim
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_smg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    noClaim :=
  ay_smg_conj_left
    (ay_smg_conj_right (ay_smg_conj_right (ay_smg_conj_right h)))

theorem ay_smg_failed_guard_audit
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_smg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    auditTranscript :=
  ay_smg_conj_right
    (ay_smg_conj_right (ay_smg_conj_right (ay_smg_conj_right h)))

theorem ay_smg_failed_submission_guard_cannot_bless_sat
    {mismatch quarantine recompute noClaim auditTranscript publicSat : Prop}
    (h : ay_smg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    ay_smg_blocks_sat noClaim publicSat :=
  fun _ => ay_smg_failed_guard_no_claim h

theorem ay_smg_failed_submission_guard_cannot_bless_unsat
    {mismatch quarantine recompute noClaim auditTranscript publicUnsat : Prop}
    (h : ay_smg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    ay_smg_blocks_unsat noClaim publicUnsat :=
  fun _ => ay_smg_failed_guard_no_claim h

theorem ay_smg_failed_guard_forces_recompute
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_smg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    recompute :=
  ay_smg_failed_guard_recompute h
