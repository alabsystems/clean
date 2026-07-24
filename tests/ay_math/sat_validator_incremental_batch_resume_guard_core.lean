-- Incremental batch-resume guard for sequential-main SAT-COMP validation.
-- Self-contained propositional contract for resumed ay validation batches.

def ay_ibrg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_ibrg_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

theorem ay_ibrg_conj_intro {left right : Prop} (hleft : left) (hright : right) :
    ay_ibrg_conj left right :=
  fun result k => k hleft hright

theorem ay_ibrg_conj_left {left right : Prop} (h : ay_ibrg_conj left right) :
    left :=
  h left (fun hleft _ => hleft)

theorem ay_ibrg_conj_right {left right : Prop} (h : ay_ibrg_conj left right) :
    right :=
  h right (fun _ hright => hright)

theorem ay_ibrg_disj_left {left right : Prop} (hleft : left) :
    ay_ibrg_disj left right :=
  fun result kleft _ => kleft hleft

theorem ay_ibrg_disj_right {left right : Prop} (hright : right) :
    ay_ibrg_disj left right :=
  fun result _ kright => kright hright

def ay_ibrg_resume_contract
    (batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (batchManifestDigest ->
      resumeCheckpointDigest ->
      completedBenchmarkSetDigest ->
      pendingBenchmarkSetDigest ->
      perResultBundleDigest ->
      checkerTranscriptDigest ->
      cacheInvalidationLedger ->
      resourceLimitManifest ->
      archiveManifest ->
      aggregationStateDigest ->
      fallbackRecomputeNoClaimPath ->
      auditTranscript ->
      result) ->
    result

theorem ay_ibrg_resume_contract_intro
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (hbatch : batchManifestDigest)
    (hcheckpoint : resumeCheckpointDigest)
    (hcompleted : completedBenchmarkSetDigest)
    (hpending : pendingBenchmarkSetDigest)
    (hbundle : perResultBundleDigest)
    (hchecker : checkerTranscriptDigest)
    (hcache : cacheInvalidationLedger)
    (hresource : resourceLimitManifest)
    (harchive : archiveManifest)
    (haggregation : aggregationStateDigest)
    (hfallback : fallbackRecomputeNoClaimPath)
    (haudit : auditTranscript) :
    ay_ibrg_resume_contract batchManifestDigest resumeCheckpointDigest
      completedBenchmarkSetDigest pendingBenchmarkSetDigest
      perResultBundleDigest checkerTranscriptDigest cacheInvalidationLedger
      resourceLimitManifest archiveManifest aggregationStateDigest
      fallbackRecomputeNoClaimPath auditTranscript :=
  fun result k =>
    k hbatch hcheckpoint hcompleted hpending hbundle hchecker hcache hresource
      harchive haggregation hfallback haudit

theorem ay_ibrg_contract_batch_manifest
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (h :
      ay_ibrg_resume_contract batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        perResultBundleDigest checkerTranscriptDigest cacheInvalidationLedger
        resourceLimitManifest archiveManifest aggregationStateDigest
        fallbackRecomputeNoClaimPath auditTranscript) :
    batchManifestDigest :=
  h batchManifestDigest (fun hbatch _ _ _ _ _ _ _ _ _ _ _ => hbatch)

theorem ay_ibrg_contract_checkpoint
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (h :
      ay_ibrg_resume_contract batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        perResultBundleDigest checkerTranscriptDigest cacheInvalidationLedger
        resourceLimitManifest archiveManifest aggregationStateDigest
        fallbackRecomputeNoClaimPath auditTranscript) :
    resumeCheckpointDigest :=
  h resumeCheckpointDigest (fun _ hcheckpoint _ _ _ _ _ _ _ _ _ _ => hcheckpoint)

theorem ay_ibrg_contract_completed_set
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (h :
      ay_ibrg_resume_contract batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        perResultBundleDigest checkerTranscriptDigest cacheInvalidationLedger
        resourceLimitManifest archiveManifest aggregationStateDigest
        fallbackRecomputeNoClaimPath auditTranscript) :
    completedBenchmarkSetDigest :=
  h completedBenchmarkSetDigest (fun _ _ hcompleted _ _ _ _ _ _ _ _ _ => hcompleted)

theorem ay_ibrg_contract_pending_set
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (h :
      ay_ibrg_resume_contract batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        perResultBundleDigest checkerTranscriptDigest cacheInvalidationLedger
        resourceLimitManifest archiveManifest aggregationStateDigest
        fallbackRecomputeNoClaimPath auditTranscript) :
    pendingBenchmarkSetDigest :=
  h pendingBenchmarkSetDigest (fun _ _ _ hpending _ _ _ _ _ _ _ _ => hpending)

theorem ay_ibrg_contract_result_bundle
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (h :
      ay_ibrg_resume_contract batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        perResultBundleDigest checkerTranscriptDigest cacheInvalidationLedger
        resourceLimitManifest archiveManifest aggregationStateDigest
        fallbackRecomputeNoClaimPath auditTranscript) :
    perResultBundleDigest :=
  h perResultBundleDigest (fun _ _ _ _ hbundle _ _ _ _ _ _ _ => hbundle)

theorem ay_ibrg_contract_checker_transcript
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (h :
      ay_ibrg_resume_contract batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        perResultBundleDigest checkerTranscriptDigest cacheInvalidationLedger
        resourceLimitManifest archiveManifest aggregationStateDigest
        fallbackRecomputeNoClaimPath auditTranscript) :
    checkerTranscriptDigest :=
  h checkerTranscriptDigest (fun _ _ _ _ _ hchecker _ _ _ _ _ _ => hchecker)

theorem ay_ibrg_contract_cache_invalidation
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (h :
      ay_ibrg_resume_contract batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        perResultBundleDigest checkerTranscriptDigest cacheInvalidationLedger
        resourceLimitManifest archiveManifest aggregationStateDigest
        fallbackRecomputeNoClaimPath auditTranscript) :
    cacheInvalidationLedger :=
  h cacheInvalidationLedger (fun _ _ _ _ _ _ hcache _ _ _ _ _ => hcache)

theorem ay_ibrg_contract_resource_limit
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (h :
      ay_ibrg_resume_contract batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        perResultBundleDigest checkerTranscriptDigest cacheInvalidationLedger
        resourceLimitManifest archiveManifest aggregationStateDigest
        fallbackRecomputeNoClaimPath auditTranscript) :
    resourceLimitManifest :=
  h resourceLimitManifest (fun _ _ _ _ _ _ _ hresource _ _ _ _ => hresource)

theorem ay_ibrg_contract_archive_manifest
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (h :
      ay_ibrg_resume_contract batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        perResultBundleDigest checkerTranscriptDigest cacheInvalidationLedger
        resourceLimitManifest archiveManifest aggregationStateDigest
        fallbackRecomputeNoClaimPath auditTranscript) :
    archiveManifest :=
  h archiveManifest (fun _ _ _ _ _ _ _ _ harchive _ _ _ => harchive)

theorem ay_ibrg_contract_aggregation_state
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (h :
      ay_ibrg_resume_contract batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        perResultBundleDigest checkerTranscriptDigest cacheInvalidationLedger
        resourceLimitManifest archiveManifest aggregationStateDigest
        fallbackRecomputeNoClaimPath auditTranscript) :
    aggregationStateDigest :=
  h aggregationStateDigest (fun _ _ _ _ _ _ _ _ _ haggr _ _ => haggr)

theorem ay_ibrg_contract_fallback_path
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (h :
      ay_ibrg_resume_contract batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        perResultBundleDigest checkerTranscriptDigest cacheInvalidationLedger
        resourceLimitManifest archiveManifest aggregationStateDigest
        fallbackRecomputeNoClaimPath auditTranscript) :
    fallbackRecomputeNoClaimPath :=
  h fallbackRecomputeNoClaimPath (fun _ _ _ _ _ _ _ _ _ _ hfallback _ => hfallback)

theorem ay_ibrg_contract_audit
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest perResultBundleDigest checkerTranscriptDigest
      cacheInvalidationLedger resourceLimitManifest archiveManifest
      aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (h :
      ay_ibrg_resume_contract batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        perResultBundleDigest checkerTranscriptDigest cacheInvalidationLedger
        resourceLimitManifest archiveManifest aggregationStateDigest
        fallbackRecomputeNoClaimPath auditTranscript) :
    auditTranscript :=
  h auditTranscript (fun _ _ _ _ _ _ _ _ _ _ _ haudit => haudit)

def ay_ibrg_resumed_row
    (resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      rowStatusPreserved originalBenchmarkClaim : Prop) : Prop :=
  ay_ibrg_conj resumeContract
    (ay_ibrg_conj cachedResultMatchesCurrentBatch
      (ay_ibrg_conj checkerBackedEvidence
        (ay_ibrg_conj rowStatusPreserved originalBenchmarkClaim)))

def ay_ibrg_sat_row_publication
    (resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      checkedSatStatus originalBenchmarkSat : Prop) : Prop :=
  ay_ibrg_resumed_row resumeContract cachedResultMatchesCurrentBatch
    checkerBackedEvidence checkedSatStatus originalBenchmarkSat

def ay_ibrg_unsat_row_publication
    (resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      checkedUnsatStatus originalBenchmarkUnsat : Prop) : Prop :=
  ay_ibrg_resumed_row resumeContract cachedResultMatchesCurrentBatch
    checkerBackedEvidence checkedUnsatStatus originalBenchmarkUnsat

theorem ay_ibrg_resumed_row_intro
    {resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      rowStatusPreserved originalBenchmarkClaim : Prop}
    (hcontract : resumeContract)
    (hcachematch : cachedResultMatchesCurrentBatch)
    (hchecker : checkerBackedEvidence)
    (hstatus : rowStatusPreserved)
    (hclaim : originalBenchmarkClaim) :
    ay_ibrg_resumed_row resumeContract cachedResultMatchesCurrentBatch
      checkerBackedEvidence rowStatusPreserved originalBenchmarkClaim :=
  ay_ibrg_conj_intro hcontract
    (ay_ibrg_conj_intro hcachematch
      (ay_ibrg_conj_intro hchecker (ay_ibrg_conj_intro hstatus hclaim)))

theorem ay_ibrg_sat_row_publication_intro
    {resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      checkedSatStatus originalBenchmarkSat : Prop}
    (hcontract : resumeContract)
    (hcachematch : cachedResultMatchesCurrentBatch)
    (hchecker : checkerBackedEvidence)
    (hstatus : checkedSatStatus)
    (hsat : originalBenchmarkSat) :
    ay_ibrg_sat_row_publication resumeContract cachedResultMatchesCurrentBatch
      checkerBackedEvidence checkedSatStatus originalBenchmarkSat :=
  ay_ibrg_resumed_row_intro hcontract hcachematch hchecker hstatus hsat

theorem ay_ibrg_unsat_row_publication_intro
    {resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      checkedUnsatStatus originalBenchmarkUnsat : Prop}
    (hcontract : resumeContract)
    (hcachematch : cachedResultMatchesCurrentBatch)
    (hchecker : checkerBackedEvidence)
    (hstatus : checkedUnsatStatus)
    (hunsat : originalBenchmarkUnsat) :
    ay_ibrg_unsat_row_publication resumeContract cachedResultMatchesCurrentBatch
      checkerBackedEvidence checkedUnsatStatus originalBenchmarkUnsat :=
  ay_ibrg_resumed_row_intro hcontract hcachematch hchecker hstatus hunsat

theorem ay_ibrg_row_resume_contract
    {resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      rowStatusPreserved originalBenchmarkClaim : Prop}
    (h :
      ay_ibrg_resumed_row resumeContract cachedResultMatchesCurrentBatch
        checkerBackedEvidence rowStatusPreserved originalBenchmarkClaim) :
    resumeContract :=
  ay_ibrg_conj_left h

theorem ay_ibrg_row_cached_result_matches_current_batch
    {resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      rowStatusPreserved originalBenchmarkClaim : Prop}
    (h :
      ay_ibrg_resumed_row resumeContract cachedResultMatchesCurrentBatch
        checkerBackedEvidence rowStatusPreserved originalBenchmarkClaim) :
    cachedResultMatchesCurrentBatch :=
  ay_ibrg_conj_left (ay_ibrg_conj_right h)

theorem ay_ibrg_row_checker_backed
    {resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      rowStatusPreserved originalBenchmarkClaim : Prop}
    (h :
      ay_ibrg_resumed_row resumeContract cachedResultMatchesCurrentBatch
        checkerBackedEvidence rowStatusPreserved originalBenchmarkClaim) :
    checkerBackedEvidence :=
  ay_ibrg_conj_left (ay_ibrg_conj_right (ay_ibrg_conj_right h))

theorem ay_ibrg_row_status_preserved
    {resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      rowStatusPreserved originalBenchmarkClaim : Prop}
    (h :
      ay_ibrg_resumed_row resumeContract cachedResultMatchesCurrentBatch
        checkerBackedEvidence rowStatusPreserved originalBenchmarkClaim) :
    rowStatusPreserved :=
  ay_ibrg_conj_left
    (ay_ibrg_conj_right (ay_ibrg_conj_right (ay_ibrg_conj_right h)))

theorem ay_ibrg_row_original_claim
    {resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      rowStatusPreserved originalBenchmarkClaim : Prop}
    (h :
      ay_ibrg_resumed_row resumeContract cachedResultMatchesCurrentBatch
        checkerBackedEvidence rowStatusPreserved originalBenchmarkClaim) :
    originalBenchmarkClaim :=
  ay_ibrg_conj_right
    (ay_ibrg_conj_right (ay_ibrg_conj_right (ay_ibrg_conj_right h)))

theorem ay_ibrg_resumed_row_requires_current_batch_match
    {resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      rowStatusPreserved originalBenchmarkClaim : Prop}
    (h :
      ay_ibrg_resumed_row resumeContract cachedResultMatchesCurrentBatch
        checkerBackedEvidence rowStatusPreserved originalBenchmarkClaim) :
    cachedResultMatchesCurrentBatch :=
  ay_ibrg_row_cached_result_matches_current_batch h

theorem ay_ibrg_resumed_row_requires_checker_evidence
    {resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      rowStatusPreserved originalBenchmarkClaim : Prop}
    (h :
      ay_ibrg_resumed_row resumeContract cachedResultMatchesCurrentBatch
        checkerBackedEvidence rowStatusPreserved originalBenchmarkClaim) :
    checkerBackedEvidence :=
  ay_ibrg_row_checker_backed h

theorem ay_ibrg_accepted_sat_row_preserves_soundness
    {resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      checkedSatStatus originalBenchmarkSat : Prop}
    (h :
      ay_ibrg_sat_row_publication resumeContract
        cachedResultMatchesCurrentBatch checkerBackedEvidence checkedSatStatus
        originalBenchmarkSat) :
    originalBenchmarkSat :=
  ay_ibrg_row_original_claim h

theorem ay_ibrg_accepted_unsat_row_preserves_soundness
    {resumeContract cachedResultMatchesCurrentBatch checkerBackedEvidence
      checkedUnsatStatus originalBenchmarkUnsat : Prop}
    (h :
      ay_ibrg_unsat_row_publication resumeContract
        cachedResultMatchesCurrentBatch checkerBackedEvidence checkedUnsatStatus
        originalBenchmarkUnsat) :
    originalBenchmarkUnsat :=
  ay_ibrg_row_original_claim h

def ay_ibrg_no_claim (diagnostic recompute auditTranscript : Prop) : Prop :=
  ay_ibrg_conj diagnostic (ay_ibrg_conj recompute auditTranscript)

theorem ay_ibrg_no_claim_intro
    {diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : diagnostic)
    (hrecompute : recompute)
    (haudit : auditTranscript) :
    ay_ibrg_no_claim diagnostic recompute auditTranscript :=
  ay_ibrg_conj_intro hdiagnostic (ay_ibrg_conj_intro hrecompute haudit)

theorem ay_ibrg_no_claim_diagnostic
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_ibrg_no_claim diagnostic recompute auditTranscript) :
    diagnostic :=
  ay_ibrg_conj_left h

theorem ay_ibrg_no_claim_recompute
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_ibrg_no_claim diagnostic recompute auditTranscript) :
    recompute :=
  ay_ibrg_conj_left (ay_ibrg_conj_right h)

theorem ay_ibrg_no_claim_audit
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_ibrg_no_claim diagnostic recompute auditTranscript) :
    auditTranscript :=
  ay_ibrg_conj_right (ay_ibrg_conj_right h)

def ay_ibrg_mismatch_forces_no_claim
    (mismatch diagnostic recompute auditTranscript : Prop) : Prop :=
  mismatch -> ay_ibrg_no_claim diagnostic recompute auditTranscript

theorem ay_ibrg_mismatch_forces_no_claim_intro
    {mismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : mismatch -> diagnostic)
    (hrecompute : mismatch -> recompute)
    (haudit : mismatch -> auditTranscript) :
    ay_ibrg_mismatch_forces_no_claim mismatch diagnostic recompute
      auditTranscript :=
  fun hmismatch =>
    ay_ibrg_no_claim_intro (hdiagnostic hmismatch) (hrecompute hmismatch)
      (haudit hmismatch)

theorem ay_ibrg_stale_checkpoint_forces_no_claim
    {staleCheckpoint diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : staleCheckpoint -> diagnostic)
    (hrecompute : staleCheckpoint -> recompute)
    (haudit : staleCheckpoint -> auditTranscript) :
    ay_ibrg_mismatch_forces_no_claim staleCheckpoint diagnostic recompute
      auditTranscript :=
  ay_ibrg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_ibrg_partial_checkpoint_forces_no_claim
    {partialCheckpoint diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : partialCheckpoint -> diagnostic)
    (hrecompute : partialCheckpoint -> recompute)
    (haudit : partialCheckpoint -> auditTranscript) :
    ay_ibrg_mismatch_forces_no_claim partialCheckpoint diagnostic recompute
      auditTranscript :=
  ay_ibrg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_ibrg_batch_manifest_mismatch_forces_no_claim
    {batchMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : batchMismatch -> diagnostic)
    (hrecompute : batchMismatch -> recompute)
    (haudit : batchMismatch -> auditTranscript) :
    ay_ibrg_mismatch_forces_no_claim batchMismatch diagnostic recompute
      auditTranscript :=
  ay_ibrg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_ibrg_result_bundle_mismatch_forces_no_claim
    {bundleMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : bundleMismatch -> diagnostic)
    (hrecompute : bundleMismatch -> recompute)
    (haudit : bundleMismatch -> auditTranscript) :
    ay_ibrg_mismatch_forces_no_claim bundleMismatch diagnostic recompute
      auditTranscript :=
  ay_ibrg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_ibrg_checker_transcript_mismatch_forces_no_claim
    {checkerMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : checkerMismatch -> diagnostic)
    (hrecompute : checkerMismatch -> recompute)
    (haudit : checkerMismatch -> auditTranscript) :
    ay_ibrg_mismatch_forces_no_claim checkerMismatch diagnostic recompute
      auditTranscript :=
  ay_ibrg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_ibrg_cache_invalidation_mismatch_forces_no_claim
    {cacheMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : cacheMismatch -> diagnostic)
    (hrecompute : cacheMismatch -> recompute)
    (haudit : cacheMismatch -> auditTranscript) :
    ay_ibrg_mismatch_forces_no_claim cacheMismatch diagnostic recompute
      auditTranscript :=
  ay_ibrg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_ibrg_resource_mismatch_forces_no_claim
    {resourceMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : resourceMismatch -> diagnostic)
    (hrecompute : resourceMismatch -> recompute)
    (haudit : resourceMismatch -> auditTranscript) :
    ay_ibrg_mismatch_forces_no_claim resourceMismatch diagnostic recompute
      auditTranscript :=
  ay_ibrg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_ibrg_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : archiveMismatch -> diagnostic)
    (hrecompute : archiveMismatch -> recompute)
    (haudit : archiveMismatch -> auditTranscript) :
    ay_ibrg_mismatch_forces_no_claim archiveMismatch diagnostic recompute
      auditTranscript :=
  ay_ibrg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_ibrg_aggregation_state_mismatch_forces_no_claim
    {aggregationMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : aggregationMismatch -> diagnostic)
    (hrecompute : aggregationMismatch -> recompute)
    (haudit : aggregationMismatch -> auditTranscript) :
    ay_ibrg_mismatch_forces_no_claim aggregationMismatch diagnostic recompute
      auditTranscript :=
  ay_ibrg_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

def ay_ibrg_resume_metadata_only
    (batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest cacheInvalidationLedger resourceLimitManifest
      archiveManifest aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (batchManifestDigest ->
      resumeCheckpointDigest ->
      completedBenchmarkSetDigest ->
      pendingBenchmarkSetDigest ->
      cacheInvalidationLedger ->
      resourceLimitManifest ->
      archiveManifest ->
      aggregationStateDigest ->
      fallbackRecomputeNoClaimPath ->
      auditTranscript ->
      result) ->
    result

theorem ay_ibrg_resume_metadata_only_intro
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest cacheInvalidationLedger resourceLimitManifest
      archiveManifest aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript : Prop}
    (hbatch : batchManifestDigest)
    (hcheckpoint : resumeCheckpointDigest)
    (hcompleted : completedBenchmarkSetDigest)
    (hpending : pendingBenchmarkSetDigest)
    (hcache : cacheInvalidationLedger)
    (hresource : resourceLimitManifest)
    (harchive : archiveManifest)
    (haggregation : aggregationStateDigest)
    (hfallback : fallbackRecomputeNoClaimPath)
    (haudit : auditTranscript) :
    ay_ibrg_resume_metadata_only batchManifestDigest resumeCheckpointDigest
      completedBenchmarkSetDigest pendingBenchmarkSetDigest cacheInvalidationLedger
      resourceLimitManifest archiveManifest aggregationStateDigest
      fallbackRecomputeNoClaimPath auditTranscript :=
  fun result k =>
    k hbatch hcheckpoint hcompleted hpending hcache hresource harchive
      haggregation hfallback haudit

def ay_ibrg_blocks_sat (noClaim publicSat : Prop) : Prop :=
  publicSat -> noClaim

def ay_ibrg_blocks_unsat (noClaim publicUnsat : Prop) : Prop :=
  publicUnsat -> noClaim

theorem ay_ibrg_resume_metadata_alone_cannot_publish_sat
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest cacheInvalidationLedger resourceLimitManifest
      archiveManifest aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript noClaim publicSat : Prop}
    (h :
      ay_ibrg_resume_metadata_only batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        cacheInvalidationLedger resourceLimitManifest archiveManifest
        aggregationStateDigest fallbackRecomputeNoClaimPath auditTranscript)
    (hnoClaim : fallbackRecomputeNoClaimPath -> noClaim) :
    ay_ibrg_blocks_sat noClaim publicSat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

theorem ay_ibrg_resume_metadata_alone_cannot_publish_unsat
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest cacheInvalidationLedger resourceLimitManifest
      archiveManifest aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript noClaim publicUnsat : Prop}
    (h :
      ay_ibrg_resume_metadata_only batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        cacheInvalidationLedger resourceLimitManifest archiveManifest
        aggregationStateDigest fallbackRecomputeNoClaimPath auditTranscript)
    (hnoClaim : fallbackRecomputeNoClaimPath -> noClaim) :
    ay_ibrg_blocks_unsat noClaim publicUnsat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

theorem ay_ibrg_resume_metadata_only_lacks_checker_evidence
    {batchManifestDigest resumeCheckpointDigest completedBenchmarkSetDigest
      pendingBenchmarkSetDigest cacheInvalidationLedger resourceLimitManifest
      archiveManifest aggregationStateDigest fallbackRecomputeNoClaimPath
      auditTranscript checkerBackedEvidence noClaim : Prop}
    (h :
      ay_ibrg_resume_metadata_only batchManifestDigest resumeCheckpointDigest
        completedBenchmarkSetDigest pendingBenchmarkSetDigest
        cacheInvalidationLedger resourceLimitManifest archiveManifest
        aggregationStateDigest fallbackRecomputeNoClaimPath auditTranscript)
    (hnoClaim : fallbackRecomputeNoClaimPath -> noClaim) :
    checkerBackedEvidence -> noClaim :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ _ _ hfallback _ => hnoClaim hfallback)

def ay_ibrg_failed_guard
    (mismatch quarantine recompute noClaim auditTranscript : Prop) : Prop :=
  ay_ibrg_conj mismatch
    (ay_ibrg_conj quarantine
      (ay_ibrg_conj recompute (ay_ibrg_conj noClaim auditTranscript)))

theorem ay_ibrg_failed_guard_intro
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (hmismatch : mismatch)
    (hquarantine : quarantine)
    (hrecompute : recompute)
    (hnoclaim : noClaim)
    (haudit : auditTranscript) :
    ay_ibrg_failed_guard mismatch quarantine recompute noClaim auditTranscript :=
  ay_ibrg_conj_intro hmismatch
    (ay_ibrg_conj_intro hquarantine
      (ay_ibrg_conj_intro hrecompute (ay_ibrg_conj_intro hnoclaim haudit)))

theorem ay_ibrg_failed_guard_mismatch
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_ibrg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    mismatch :=
  ay_ibrg_conj_left h

theorem ay_ibrg_failed_guard_recompute
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_ibrg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    recompute :=
  ay_ibrg_conj_left (ay_ibrg_conj_right (ay_ibrg_conj_right h))

theorem ay_ibrg_failed_guard_no_claim
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_ibrg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    noClaim :=
  ay_ibrg_conj_left
    (ay_ibrg_conj_right (ay_ibrg_conj_right (ay_ibrg_conj_right h)))

theorem ay_ibrg_failed_guard_audit
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_ibrg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    auditTranscript :=
  ay_ibrg_conj_right
    (ay_ibrg_conj_right (ay_ibrg_conj_right (ay_ibrg_conj_right h)))

theorem ay_ibrg_failed_resume_guard_cannot_bless_sat
    {mismatch quarantine recompute noClaim auditTranscript publicSat : Prop}
    (h : ay_ibrg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    ay_ibrg_blocks_sat noClaim publicSat :=
  fun _ => ay_ibrg_failed_guard_no_claim h

theorem ay_ibrg_failed_resume_guard_cannot_bless_unsat
    {mismatch quarantine recompute noClaim auditTranscript publicUnsat : Prop}
    (h : ay_ibrg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    ay_ibrg_blocks_unsat noClaim publicUnsat :=
  fun _ => ay_ibrg_failed_guard_no_claim h

theorem ay_ibrg_failed_guard_forces_recompute
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_ibrg_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    recompute :=
  ay_ibrg_failed_guard_recompute h
