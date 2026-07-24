-- Result-table aggregation guard for sequential-main SAT-COMP reporting.
-- Self-contained propositional contract for CSV/JSON tables derived from
-- per-benchmark validated ay result bundles.

def ay_rtag_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_rtag_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

theorem ay_rtag_conj_intro {left right : Prop} (hleft : left) (hright : right) :
    ay_rtag_conj left right :=
  fun result k => k hleft hright

theorem ay_rtag_conj_left {left right : Prop} (h : ay_rtag_conj left right) :
    left :=
  h left (fun hleft _ => hleft)

theorem ay_rtag_conj_right {left right : Prop} (h : ay_rtag_conj left right) :
    right :=
  h right (fun _ hright => hright)

theorem ay_rtag_disj_left {left right : Prop} (hleft : left) :
    ay_rtag_disj left right :=
  fun result kleft _ => kleft hleft

theorem ay_rtag_disj_right {left right : Prop} (hright : right) :
    ay_rtag_disj left right :=
  fun result _ kright => kright hright

def ay_rtag_table_contract
    (benchmarkListDigest perBenchmarkValidatedBundleDigest
      aggregationScriptDigest tableSchemaVersionDigest rowOrderingDigest
      statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest checkerTranscriptReferences
      auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (benchmarkListDigest ->
      perBenchmarkValidatedBundleDigest ->
      aggregationScriptDigest ->
      tableSchemaVersionDigest ->
      rowOrderingDigest ->
      statusNormalizationLedger ->
      scoreCountSummaryDigest ->
      noClaimPropagationLedger ->
      archiveUploadManifest ->
      checkerTranscriptReferences ->
      auditTranscript ->
      result) ->
    result

theorem ay_rtag_table_contract_intro
    {benchmarkListDigest perBenchmarkValidatedBundleDigest
      aggregationScriptDigest tableSchemaVersionDigest rowOrderingDigest
      statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest checkerTranscriptReferences
      auditTranscript : Prop}
    (hbenchmarks : benchmarkListDigest)
    (hbundle : perBenchmarkValidatedBundleDigest)
    (hscript : aggregationScriptDigest)
    (hschema : tableSchemaVersionDigest)
    (hrows : rowOrderingDigest)
    (hstatus : statusNormalizationLedger)
    (hscore : scoreCountSummaryDigest)
    (hnoclaim : noClaimPropagationLedger)
    (harchive : archiveUploadManifest)
    (hcheckerRefs : checkerTranscriptReferences)
    (haudit : auditTranscript) :
    ay_rtag_table_contract benchmarkListDigest
      perBenchmarkValidatedBundleDigest aggregationScriptDigest
      tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
      scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
      checkerTranscriptReferences auditTranscript :=
  fun result k =>
    k hbenchmarks hbundle hscript hschema hrows hstatus hscore hnoclaim
      harchive hcheckerRefs haudit

theorem ay_rtag_contract_benchmark_list
    {benchmarkListDigest perBenchmarkValidatedBundleDigest
      aggregationScriptDigest tableSchemaVersionDigest rowOrderingDigest
      statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest checkerTranscriptReferences
      auditTranscript : Prop}
    (h :
      ay_rtag_table_contract benchmarkListDigest
        perBenchmarkValidatedBundleDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        checkerTranscriptReferences auditTranscript) :
    benchmarkListDigest :=
  h benchmarkListDigest (fun hbenchmarks _ _ _ _ _ _ _ _ _ _ => hbenchmarks)

theorem ay_rtag_contract_validated_bundle
    {benchmarkListDigest perBenchmarkValidatedBundleDigest
      aggregationScriptDigest tableSchemaVersionDigest rowOrderingDigest
      statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest checkerTranscriptReferences
      auditTranscript : Prop}
    (h :
      ay_rtag_table_contract benchmarkListDigest
        perBenchmarkValidatedBundleDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        checkerTranscriptReferences auditTranscript) :
    perBenchmarkValidatedBundleDigest :=
  h perBenchmarkValidatedBundleDigest (fun _ hbundle _ _ _ _ _ _ _ _ _ => hbundle)

theorem ay_rtag_contract_aggregation_script
    {benchmarkListDigest perBenchmarkValidatedBundleDigest
      aggregationScriptDigest tableSchemaVersionDigest rowOrderingDigest
      statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest checkerTranscriptReferences
      auditTranscript : Prop}
    (h :
      ay_rtag_table_contract benchmarkListDigest
        perBenchmarkValidatedBundleDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        checkerTranscriptReferences auditTranscript) :
    aggregationScriptDigest :=
  h aggregationScriptDigest (fun _ _ hscript _ _ _ _ _ _ _ _ => hscript)

theorem ay_rtag_contract_schema
    {benchmarkListDigest perBenchmarkValidatedBundleDigest
      aggregationScriptDigest tableSchemaVersionDigest rowOrderingDigest
      statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest checkerTranscriptReferences
      auditTranscript : Prop}
    (h :
      ay_rtag_table_contract benchmarkListDigest
        perBenchmarkValidatedBundleDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        checkerTranscriptReferences auditTranscript) :
    tableSchemaVersionDigest :=
  h tableSchemaVersionDigest (fun _ _ _ hschema _ _ _ _ _ _ _ => hschema)

theorem ay_rtag_contract_row_ordering
    {benchmarkListDigest perBenchmarkValidatedBundleDigest
      aggregationScriptDigest tableSchemaVersionDigest rowOrderingDigest
      statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest checkerTranscriptReferences
      auditTranscript : Prop}
    (h :
      ay_rtag_table_contract benchmarkListDigest
        perBenchmarkValidatedBundleDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        checkerTranscriptReferences auditTranscript) :
    rowOrderingDigest :=
  h rowOrderingDigest (fun _ _ _ _ hrows _ _ _ _ _ _ => hrows)

theorem ay_rtag_contract_status_normalization
    {benchmarkListDigest perBenchmarkValidatedBundleDigest
      aggregationScriptDigest tableSchemaVersionDigest rowOrderingDigest
      statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest checkerTranscriptReferences
      auditTranscript : Prop}
    (h :
      ay_rtag_table_contract benchmarkListDigest
        perBenchmarkValidatedBundleDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        checkerTranscriptReferences auditTranscript) :
    statusNormalizationLedger :=
  h statusNormalizationLedger (fun _ _ _ _ _ hstatus _ _ _ _ _ => hstatus)

theorem ay_rtag_contract_score_summary
    {benchmarkListDigest perBenchmarkValidatedBundleDigest
      aggregationScriptDigest tableSchemaVersionDigest rowOrderingDigest
      statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest checkerTranscriptReferences
      auditTranscript : Prop}
    (h :
      ay_rtag_table_contract benchmarkListDigest
        perBenchmarkValidatedBundleDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        checkerTranscriptReferences auditTranscript) :
    scoreCountSummaryDigest :=
  h scoreCountSummaryDigest (fun _ _ _ _ _ _ hscore _ _ _ _ => hscore)

theorem ay_rtag_contract_no_claim_propagation
    {benchmarkListDigest perBenchmarkValidatedBundleDigest
      aggregationScriptDigest tableSchemaVersionDigest rowOrderingDigest
      statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest checkerTranscriptReferences
      auditTranscript : Prop}
    (h :
      ay_rtag_table_contract benchmarkListDigest
        perBenchmarkValidatedBundleDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        checkerTranscriptReferences auditTranscript) :
    noClaimPropagationLedger :=
  h noClaimPropagationLedger (fun _ _ _ _ _ _ _ hnoclaim _ _ _ => hnoclaim)

theorem ay_rtag_contract_archive_upload
    {benchmarkListDigest perBenchmarkValidatedBundleDigest
      aggregationScriptDigest tableSchemaVersionDigest rowOrderingDigest
      statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest checkerTranscriptReferences
      auditTranscript : Prop}
    (h :
      ay_rtag_table_contract benchmarkListDigest
        perBenchmarkValidatedBundleDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        checkerTranscriptReferences auditTranscript) :
    archiveUploadManifest :=
  h archiveUploadManifest (fun _ _ _ _ _ _ _ _ harchive _ _ => harchive)

theorem ay_rtag_contract_checker_refs
    {benchmarkListDigest perBenchmarkValidatedBundleDigest
      aggregationScriptDigest tableSchemaVersionDigest rowOrderingDigest
      statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest checkerTranscriptReferences
      auditTranscript : Prop}
    (h :
      ay_rtag_table_contract benchmarkListDigest
        perBenchmarkValidatedBundleDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        checkerTranscriptReferences auditTranscript) :
    checkerTranscriptReferences :=
  h checkerTranscriptReferences (fun _ _ _ _ _ _ _ _ _ hrefs _ => hrefs)

theorem ay_rtag_contract_audit
    {benchmarkListDigest perBenchmarkValidatedBundleDigest
      aggregationScriptDigest tableSchemaVersionDigest rowOrderingDigest
      statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest checkerTranscriptReferences
      auditTranscript : Prop}
    (h :
      ay_rtag_table_contract benchmarkListDigest
        perBenchmarkValidatedBundleDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        checkerTranscriptReferences auditTranscript) :
    auditTranscript :=
  h auditTranscript (fun _ _ _ _ _ _ _ _ _ _ haudit => haudit)

def ay_rtag_validated_table_row
    (tableContract perRowValidatedBundle checkerBackedBundle statusPreserved
      originalBenchmarkClaim : Prop) : Prop :=
  ay_rtag_conj tableContract
    (ay_rtag_conj perRowValidatedBundle
      (ay_rtag_conj checkerBackedBundle
        (ay_rtag_conj statusPreserved originalBenchmarkClaim)))

def ay_rtag_sat_row_publication
    (tableContract perRowValidatedBundle checkerBackedBundle checkedSatStatus
      originalBenchmarkSat : Prop) : Prop :=
  ay_rtag_validated_table_row tableContract perRowValidatedBundle
    checkerBackedBundle checkedSatStatus originalBenchmarkSat

def ay_rtag_unsat_row_publication
    (tableContract perRowValidatedBundle checkerBackedBundle checkedUnsatStatus
      originalBenchmarkUnsat : Prop) : Prop :=
  ay_rtag_validated_table_row tableContract perRowValidatedBundle
    checkerBackedBundle checkedUnsatStatus originalBenchmarkUnsat

theorem ay_rtag_validated_table_row_intro
    {tableContract perRowValidatedBundle checkerBackedBundle statusPreserved
      originalBenchmarkClaim : Prop}
    (hcontract : tableContract)
    (hbundle : perRowValidatedBundle)
    (hchecker : checkerBackedBundle)
    (hstatus : statusPreserved)
    (hclaim : originalBenchmarkClaim) :
    ay_rtag_validated_table_row tableContract perRowValidatedBundle
      checkerBackedBundle statusPreserved originalBenchmarkClaim :=
  ay_rtag_conj_intro hcontract
    (ay_rtag_conj_intro hbundle
      (ay_rtag_conj_intro hchecker (ay_rtag_conj_intro hstatus hclaim)))

theorem ay_rtag_sat_row_publication_intro
    {tableContract perRowValidatedBundle checkerBackedBundle checkedSatStatus
      originalBenchmarkSat : Prop}
    (hcontract : tableContract)
    (hbundle : perRowValidatedBundle)
    (hchecker : checkerBackedBundle)
    (hstatus : checkedSatStatus)
    (hsat : originalBenchmarkSat) :
    ay_rtag_sat_row_publication tableContract perRowValidatedBundle
      checkerBackedBundle checkedSatStatus originalBenchmarkSat :=
  ay_rtag_validated_table_row_intro hcontract hbundle hchecker hstatus hsat

theorem ay_rtag_unsat_row_publication_intro
    {tableContract perRowValidatedBundle checkerBackedBundle checkedUnsatStatus
      originalBenchmarkUnsat : Prop}
    (hcontract : tableContract)
    (hbundle : perRowValidatedBundle)
    (hchecker : checkerBackedBundle)
    (hstatus : checkedUnsatStatus)
    (hunsat : originalBenchmarkUnsat) :
    ay_rtag_unsat_row_publication tableContract perRowValidatedBundle
      checkerBackedBundle checkedUnsatStatus originalBenchmarkUnsat :=
  ay_rtag_validated_table_row_intro hcontract hbundle hchecker hstatus hunsat

theorem ay_rtag_row_contract
    {tableContract perRowValidatedBundle checkerBackedBundle statusPreserved
      originalBenchmarkClaim : Prop}
    (h :
      ay_rtag_validated_table_row tableContract perRowValidatedBundle
        checkerBackedBundle statusPreserved originalBenchmarkClaim) :
    tableContract :=
  ay_rtag_conj_left h

theorem ay_rtag_row_validated_bundle
    {tableContract perRowValidatedBundle checkerBackedBundle statusPreserved
      originalBenchmarkClaim : Prop}
    (h :
      ay_rtag_validated_table_row tableContract perRowValidatedBundle
        checkerBackedBundle statusPreserved originalBenchmarkClaim) :
    perRowValidatedBundle :=
  ay_rtag_conj_left (ay_rtag_conj_right h)

theorem ay_rtag_row_checker_backed
    {tableContract perRowValidatedBundle checkerBackedBundle statusPreserved
      originalBenchmarkClaim : Prop}
    (h :
      ay_rtag_validated_table_row tableContract perRowValidatedBundle
        checkerBackedBundle statusPreserved originalBenchmarkClaim) :
    checkerBackedBundle :=
  ay_rtag_conj_left (ay_rtag_conj_right (ay_rtag_conj_right h))

theorem ay_rtag_row_status_preserved
    {tableContract perRowValidatedBundle checkerBackedBundle statusPreserved
      originalBenchmarkClaim : Prop}
    (h :
      ay_rtag_validated_table_row tableContract perRowValidatedBundle
        checkerBackedBundle statusPreserved originalBenchmarkClaim) :
    statusPreserved :=
  ay_rtag_conj_left
    (ay_rtag_conj_right (ay_rtag_conj_right (ay_rtag_conj_right h)))

theorem ay_rtag_row_original_claim
    {tableContract perRowValidatedBundle checkerBackedBundle statusPreserved
      originalBenchmarkClaim : Prop}
    (h :
      ay_rtag_validated_table_row tableContract perRowValidatedBundle
        checkerBackedBundle statusPreserved originalBenchmarkClaim) :
    originalBenchmarkClaim :=
  ay_rtag_conj_right
    (ay_rtag_conj_right (ay_rtag_conj_right (ay_rtag_conj_right h)))

theorem ay_rtag_each_accepted_row_tied_to_validated_bundle
    {tableContract perRowValidatedBundle checkerBackedBundle statusPreserved
      originalBenchmarkClaim : Prop}
    (h :
      ay_rtag_validated_table_row tableContract perRowValidatedBundle
        checkerBackedBundle statusPreserved originalBenchmarkClaim) :
    perRowValidatedBundle :=
  ay_rtag_row_validated_bundle h

theorem ay_rtag_each_accepted_row_has_checker_backed_bundle
    {tableContract perRowValidatedBundle checkerBackedBundle statusPreserved
      originalBenchmarkClaim : Prop}
    (h :
      ay_rtag_validated_table_row tableContract perRowValidatedBundle
        checkerBackedBundle statusPreserved originalBenchmarkClaim) :
    checkerBackedBundle :=
  ay_rtag_row_checker_backed h

theorem ay_rtag_accepted_sat_row_preserves_soundness
    {tableContract perRowValidatedBundle checkerBackedBundle checkedSatStatus
      originalBenchmarkSat : Prop}
    (h :
      ay_rtag_sat_row_publication tableContract perRowValidatedBundle
        checkerBackedBundle checkedSatStatus originalBenchmarkSat) :
    originalBenchmarkSat :=
  ay_rtag_row_original_claim h

theorem ay_rtag_accepted_unsat_row_preserves_soundness
    {tableContract perRowValidatedBundle checkerBackedBundle checkedUnsatStatus
      originalBenchmarkUnsat : Prop}
    (h :
      ay_rtag_unsat_row_publication tableContract perRowValidatedBundle
        checkerBackedBundle checkedUnsatStatus originalBenchmarkUnsat) :
    originalBenchmarkUnsat :=
  ay_rtag_row_original_claim h

def ay_rtag_no_claim (diagnostic recompute auditTranscript : Prop) : Prop :=
  ay_rtag_conj diagnostic (ay_rtag_conj recompute auditTranscript)

theorem ay_rtag_no_claim_intro
    {diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : diagnostic)
    (hrecompute : recompute)
    (haudit : auditTranscript) :
    ay_rtag_no_claim diagnostic recompute auditTranscript :=
  ay_rtag_conj_intro hdiagnostic (ay_rtag_conj_intro hrecompute haudit)

theorem ay_rtag_no_claim_diagnostic
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_rtag_no_claim diagnostic recompute auditTranscript) :
    diagnostic :=
  ay_rtag_conj_left h

theorem ay_rtag_no_claim_recompute
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_rtag_no_claim diagnostic recompute auditTranscript) :
    recompute :=
  ay_rtag_conj_left (ay_rtag_conj_right h)

theorem ay_rtag_no_claim_audit
    {diagnostic recompute auditTranscript : Prop}
    (h : ay_rtag_no_claim diagnostic recompute auditTranscript) :
    auditTranscript :=
  ay_rtag_conj_right (ay_rtag_conj_right h)

def ay_rtag_mismatch_forces_no_claim
    (mismatch diagnostic recompute auditTranscript : Prop) : Prop :=
  mismatch -> ay_rtag_no_claim diagnostic recompute auditTranscript

theorem ay_rtag_mismatch_forces_no_claim_intro
    {mismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : mismatch -> diagnostic)
    (hrecompute : mismatch -> recompute)
    (haudit : mismatch -> auditTranscript) :
    ay_rtag_mismatch_forces_no_claim mismatch diagnostic recompute
      auditTranscript :=
  fun hmismatch =>
    ay_rtag_no_claim_intro (hdiagnostic hmismatch) (hrecompute hmismatch)
      (haudit hmismatch)

theorem ay_rtag_aggregation_mismatch_forces_no_claim
    {aggregationMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : aggregationMismatch -> diagnostic)
    (hrecompute : aggregationMismatch -> recompute)
    (haudit : aggregationMismatch -> auditTranscript) :
    ay_rtag_mismatch_forces_no_claim aggregationMismatch diagnostic recompute
      auditTranscript :=
  ay_rtag_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_rtag_table_mismatch_forces_no_claim
    {tableMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : tableMismatch -> diagnostic)
    (hrecompute : tableMismatch -> recompute)
    (haudit : tableMismatch -> auditTranscript) :
    ay_rtag_mismatch_forces_no_claim tableMismatch diagnostic recompute
      auditTranscript :=
  ay_rtag_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_rtag_status_mismatch_forces_no_claim
    {statusMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : statusMismatch -> diagnostic)
    (hrecompute : statusMismatch -> recompute)
    (haudit : statusMismatch -> auditTranscript) :
    ay_rtag_mismatch_forces_no_claim statusMismatch diagnostic recompute
      auditTranscript :=
  ay_rtag_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_rtag_row_order_mismatch_forces_no_claim
    {rowOrderMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : rowOrderMismatch -> diagnostic)
    (hrecompute : rowOrderMismatch -> recompute)
    (haudit : rowOrderMismatch -> auditTranscript) :
    ay_rtag_mismatch_forces_no_claim rowOrderMismatch diagnostic recompute
      auditTranscript :=
  ay_rtag_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_rtag_score_mismatch_forces_no_claim
    {scoreMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : scoreMismatch -> diagnostic)
    (hrecompute : scoreMismatch -> recompute)
    (haudit : scoreMismatch -> auditTranscript) :
    ay_rtag_mismatch_forces_no_claim scoreMismatch diagnostic recompute
      auditTranscript :=
  ay_rtag_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_rtag_archive_mismatch_forces_no_claim
    {archiveMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : archiveMismatch -> diagnostic)
    (hrecompute : archiveMismatch -> recompute)
    (haudit : archiveMismatch -> auditTranscript) :
    ay_rtag_mismatch_forces_no_claim archiveMismatch diagnostic recompute
      auditTranscript :=
  ay_rtag_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

theorem ay_rtag_audit_mismatch_forces_no_claim
    {auditMismatch diagnostic recompute auditTranscript : Prop}
    (hdiagnostic : auditMismatch -> diagnostic)
    (hrecompute : auditMismatch -> recompute)
    (haudit : auditMismatch -> auditTranscript) :
    ay_rtag_mismatch_forces_no_claim auditMismatch diagnostic recompute
      auditTranscript :=
  ay_rtag_mismatch_forces_no_claim_intro hdiagnostic hrecompute haudit

def ay_rtag_table_only_evidence
    (benchmarkListDigest aggregationScriptDigest tableSchemaVersionDigest
      rowOrderingDigest statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest auditTranscript : Prop) :
    Prop :=
  forall result : Prop,
    (benchmarkListDigest ->
      aggregationScriptDigest ->
      tableSchemaVersionDigest ->
      rowOrderingDigest ->
      statusNormalizationLedger ->
      scoreCountSummaryDigest ->
      noClaimPropagationLedger ->
      archiveUploadManifest ->
      auditTranscript ->
      result) ->
    result

theorem ay_rtag_table_only_evidence_intro
    {benchmarkListDigest aggregationScriptDigest tableSchemaVersionDigest
      rowOrderingDigest statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest auditTranscript : Prop}
    (hbenchmarks : benchmarkListDigest)
    (hscript : aggregationScriptDigest)
    (hschema : tableSchemaVersionDigest)
    (hrows : rowOrderingDigest)
    (hstatus : statusNormalizationLedger)
    (hscore : scoreCountSummaryDigest)
    (hnoclaim : noClaimPropagationLedger)
    (harchive : archiveUploadManifest)
    (haudit : auditTranscript) :
    ay_rtag_table_only_evidence benchmarkListDigest aggregationScriptDigest
      tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
      scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
      auditTranscript :=
  fun result k =>
    k hbenchmarks hscript hschema hrows hstatus hscore hnoclaim harchive
      haudit

def ay_rtag_blocks_sat (noClaim publicSat : Prop) : Prop :=
  publicSat -> noClaim

def ay_rtag_blocks_unsat (noClaim publicUnsat : Prop) : Prop :=
  publicUnsat -> noClaim

theorem ay_rtag_aggregated_table_alone_cannot_publish_sat
    {benchmarkListDigest aggregationScriptDigest tableSchemaVersionDigest
      rowOrderingDigest statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest auditTranscript noClaim
      publicSat : Prop}
    (h :
      ay_rtag_table_only_evidence benchmarkListDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        auditTranscript)
    (hnoClaim : noClaimPropagationLedger -> noClaim) :
    ay_rtag_blocks_sat noClaim publicSat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ hledger _ _ => hnoClaim hledger)

theorem ay_rtag_aggregated_table_alone_cannot_publish_unsat
    {benchmarkListDigest aggregationScriptDigest tableSchemaVersionDigest
      rowOrderingDigest statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest auditTranscript noClaim
      publicUnsat : Prop}
    (h :
      ay_rtag_table_only_evidence benchmarkListDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        auditTranscript)
    (hnoClaim : noClaimPropagationLedger -> noClaim) :
    ay_rtag_blocks_unsat noClaim publicUnsat :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ hledger _ _ => hnoClaim hledger)

theorem ay_rtag_table_only_lacks_checker_backed_bundle
    {benchmarkListDigest aggregationScriptDigest tableSchemaVersionDigest
      rowOrderingDigest statusNormalizationLedger scoreCountSummaryDigest
      noClaimPropagationLedger archiveUploadManifest auditTranscript
      checkerBackedBundle noClaim : Prop}
    (h :
      ay_rtag_table_only_evidence benchmarkListDigest aggregationScriptDigest
        tableSchemaVersionDigest rowOrderingDigest statusNormalizationLedger
        scoreCountSummaryDigest noClaimPropagationLedger archiveUploadManifest
        auditTranscript)
    (hnoClaim : noClaimPropagationLedger -> noClaim) :
    checkerBackedBundle -> noClaim :=
  fun _ =>
    h noClaim (fun _ _ _ _ _ _ hledger _ _ => hnoClaim hledger)

def ay_rtag_failed_guard
    (mismatch quarantine recompute noClaim auditTranscript : Prop) : Prop :=
  ay_rtag_conj mismatch
    (ay_rtag_conj quarantine
      (ay_rtag_conj recompute (ay_rtag_conj noClaim auditTranscript)))

theorem ay_rtag_failed_guard_intro
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (hmismatch : mismatch)
    (hquarantine : quarantine)
    (hrecompute : recompute)
    (hnoclaim : noClaim)
    (haudit : auditTranscript) :
    ay_rtag_failed_guard mismatch quarantine recompute noClaim auditTranscript :=
  ay_rtag_conj_intro hmismatch
    (ay_rtag_conj_intro hquarantine
      (ay_rtag_conj_intro hrecompute (ay_rtag_conj_intro hnoclaim haudit)))

theorem ay_rtag_failed_guard_mismatch
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_rtag_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    mismatch :=
  ay_rtag_conj_left h

theorem ay_rtag_failed_guard_recompute
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_rtag_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    recompute :=
  ay_rtag_conj_left (ay_rtag_conj_right (ay_rtag_conj_right h))

theorem ay_rtag_failed_guard_no_claim
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_rtag_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    noClaim :=
  ay_rtag_conj_left
    (ay_rtag_conj_right (ay_rtag_conj_right (ay_rtag_conj_right h)))

theorem ay_rtag_failed_guard_audit
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_rtag_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    auditTranscript :=
  ay_rtag_conj_right
    (ay_rtag_conj_right (ay_rtag_conj_right (ay_rtag_conj_right h)))

theorem ay_rtag_failed_aggregation_guard_cannot_bless_sat
    {mismatch quarantine recompute noClaim auditTranscript publicSat : Prop}
    (h : ay_rtag_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    ay_rtag_blocks_sat noClaim publicSat :=
  fun _ => ay_rtag_failed_guard_no_claim h

theorem ay_rtag_failed_aggregation_guard_cannot_bless_unsat
    {mismatch quarantine recompute noClaim auditTranscript publicUnsat : Prop}
    (h : ay_rtag_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    ay_rtag_blocks_unsat noClaim publicUnsat :=
  fun _ => ay_rtag_failed_guard_no_claim h

theorem ay_rtag_failed_guard_forces_recompute
    {mismatch quarantine recompute noClaim auditTranscript : Prop}
    (h : ay_rtag_failed_guard mismatch quarantine recompute noClaim auditTranscript) :
    recompute :=
  ay_rtag_failed_guard_recompute h
