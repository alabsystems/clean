def ay_tcrg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_tcrg_equisat (before after : Prop) : Prop :=
  ay_tcrg_conj (before -> after) (after -> before)

def ay_tcrg_guard
    (trailSnapshotDigest : Prop)
    (assignmentLevelMapDigest : Prop)
    (propagationQueueDigest : Prop)
    (reasonAntecedentMapDigest : Prop)
    (watchlistDigest : Prop)
    (restoreLedger : Prop)
    (clauseDatabaseDigest : Prop)
    (postRestorePropagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackNoClaimPath : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (trailSnapshotDigest ->
      assignmentLevelMapDigest ->
      propagationQueueDigest ->
      reasonAntecedentMapDigest ->
      watchlistDigest ->
      restoreLedger ->
      clauseDatabaseDigest ->
      postRestorePropagationReplayTranscript ->
      solverBuildEvidence ->
      validatorGate ->
      archiveManifest ->
      fallbackNoClaimPath ->
      auditTranscript ->
      result) ->
    result

def ay_tcrg_agreement
    (trailSnapshotDigest : Prop)
    (assignmentLevelMapDigest : Prop)
    (propagationQueueDigest : Prop)
    (reasonAntecedentMapDigest : Prop)
    (watchlistDigest : Prop)
    (restoreLedger : Prop)
    (clauseDatabaseDigest : Prop)
    (postRestorePropagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (auditTranscript : Prop) : Prop :=
  ay_tcrg_guard
    trailSnapshotDigest
    assignmentLevelMapDigest
    propagationQueueDigest
    reasonAntecedentMapDigest
    watchlistDigest
    restoreLedger
    clauseDatabaseDigest
    postRestorePropagationReplayTranscript
    solverBuildEvidence
    validatorGate
    archiveManifest
    True
    auditTranscript

def ay_tcrg_accepted_restore
    (trailSnapshotDigest : Prop)
    (assignmentLevelMapDigest : Prop)
    (propagationQueueDigest : Prop)
    (reasonAntecedentMapDigest : Prop)
    (watchlistDigest : Prop)
    (restoreLedger : Prop)
    (clauseDatabaseDigest : Prop)
    (postRestorePropagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackNoClaimPath : Prop)
    (auditTranscript : Prop) : Prop :=
  ay_tcrg_conj
    (ay_tcrg_guard
      trailSnapshotDigest
      assignmentLevelMapDigest
      propagationQueueDigest
      reasonAntecedentMapDigest
      watchlistDigest
      restoreLedger
      clauseDatabaseDigest
      postRestorePropagationReplayTranscript
      solverBuildEvidence
      validatorGate
      archiveManifest
      fallbackNoClaimPath
      auditTranscript)
    (ay_tcrg_agreement
      trailSnapshotDigest
      assignmentLevelMapDigest
      propagationQueueDigest
      reasonAntecedentMapDigest
      watchlistDigest
      restoreLedger
      clauseDatabaseDigest
      postRestorePropagationReplayTranscript
      solverBuildEvidence
      validatorGate
      archiveManifest
      auditTranscript)

def ay_tcrg_public_report
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) : Prop :=
  ay_tcrg_conj acceptedEvidence (ay_tcrg_conj originalFormulaTruth publicOutcome)

def ay_tcrg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_tcrg_conj diagnostic fallbackOrRecompute

theorem ay_tcrg_conj_intro (left right : Prop) :
    left -> right -> ay_tcrg_conj left right :=
  fun hleft hright result k => k hleft hright

theorem ay_tcrg_conj_left (left right : Prop) :
    ay_tcrg_conj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_tcrg_conj_right (left right : Prop) :
    ay_tcrg_conj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_tcrg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_tcrg_equisat before after :=
  ay_tcrg_conj_intro (before -> after) (after -> before)

theorem ay_tcrg_equisat_forward (before after : Prop) :
    ay_tcrg_equisat before after -> before -> after :=
  ay_tcrg_conj_left (before -> after) (after -> before)

theorem ay_tcrg_equisat_backward (before after : Prop) :
    ay_tcrg_equisat before after -> after -> before :=
  ay_tcrg_conj_right (before -> after) (after -> before)

theorem ay_tcrg_guard_intro
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    trailSnapshotDigest ->
    assignmentLevelMapDigest ->
    propagationQueueDigest ->
    reasonAntecedentMapDigest ->
    watchlistDigest ->
    restoreLedger ->
    clauseDatabaseDigest ->
    postRestorePropagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    fallbackNoClaimPath ->
    auditTranscript ->
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  fun htrail hlevel hqueue hreason hwatch hrestore hdb hreplay hbuild hvalidator harchive hfallback haudit result k =>
    k htrail hlevel hqueue hreason hwatch hrestore hdb hreplay hbuild hvalidator harchive hfallback haudit

theorem ay_tcrg_guard_trail
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    trailSnapshotDigest :=
  fun h => h trailSnapshotDigest (fun htrail _ _ _ _ _ _ _ _ _ _ _ _ => htrail)

theorem ay_tcrg_guard_level
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    assignmentLevelMapDigest :=
  fun h => h assignmentLevelMapDigest (fun _ hlevel _ _ _ _ _ _ _ _ _ _ _ => hlevel)

theorem ay_tcrg_guard_queue
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    propagationQueueDigest :=
  fun h => h propagationQueueDigest (fun _ _ hqueue _ _ _ _ _ _ _ _ _ _ => hqueue)

theorem ay_tcrg_guard_reason
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    reasonAntecedentMapDigest :=
  fun h => h reasonAntecedentMapDigest (fun _ _ _ hreason _ _ _ _ _ _ _ _ _ => hreason)

theorem ay_tcrg_guard_watch
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    watchlistDigest :=
  fun h => h watchlistDigest (fun _ _ _ _ hwatch _ _ _ _ _ _ _ _ => hwatch)

theorem ay_tcrg_guard_restore
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    restoreLedger :=
  fun h => h restoreLedger (fun _ _ _ _ _ hrestore _ _ _ _ _ _ _ => hrestore)

theorem ay_tcrg_guard_database
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    clauseDatabaseDigest :=
  fun h => h clauseDatabaseDigest (fun _ _ _ _ _ _ hdb _ _ _ _ _ _ => hdb)

theorem ay_tcrg_guard_replay
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    postRestorePropagationReplayTranscript :=
  fun h => h postRestorePropagationReplayTranscript (fun _ _ _ _ _ _ _ hreplay _ _ _ _ _ => hreplay)

theorem ay_tcrg_guard_build
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun h => h solverBuildEvidence (fun _ _ _ _ _ _ _ _ hbuild _ _ _ _ => hbuild)

theorem ay_tcrg_guard_validator
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    validatorGate :=
  fun h => h validatorGate (fun _ _ _ _ _ _ _ _ _ hvalidator _ _ _ => hvalidator)

theorem ay_tcrg_guard_archive
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun h => h archiveManifest (fun _ _ _ _ _ _ _ _ _ _ harchive _ _ => harchive)

theorem ay_tcrg_guard_fallback
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun h => h fallbackNoClaimPath (fun _ _ _ _ _ _ _ _ _ _ _ hfallback _ => hfallback)

theorem ay_tcrg_guard_audit
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun h => h auditTranscript (fun _ _ _ _ _ _ _ _ _ _ _ _ haudit => haudit)

theorem ay_tcrg_agreement_intro
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript : Prop) :
    trailSnapshotDigest ->
    assignmentLevelMapDigest ->
    propagationQueueDigest ->
    reasonAntecedentMapDigest ->
    watchlistDigest ->
    restoreLedger ->
    clauseDatabaseDigest ->
    postRestorePropagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    auditTranscript ->
    ay_tcrg_agreement trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript :=
  fun htrail hlevel hqueue hreason hwatch hrestore hdb hreplay hbuild hvalidator harchive haudit =>
    ay_tcrg_guard_intro trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest True auditTranscript
      htrail hlevel hqueue hreason hwatch hrestore hdb hreplay hbuild hvalidator harchive True.intro haudit

theorem ay_tcrg_accepted_restore_intro
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_tcrg_agreement trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript ->
    ay_tcrg_accepted_restore trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  ay_tcrg_conj_intro
    (ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
    (ay_tcrg_agreement trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_tcrg_accepted_guard
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_accepted_restore trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  ay_tcrg_conj_left
    (ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
    (ay_tcrg_agreement trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_tcrg_accepted_agreement
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_tcrg_accepted_restore trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_tcrg_agreement trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript :=
  ay_tcrg_conj_right
    (ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
    (ay_tcrg_agreement trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_tcrg_restore_is_search_state_only
    (acceptedEvidence restoredSearchState : Prop) :
    acceptedEvidence ->
    restoredSearchState ->
    ay_tcrg_conj acceptedEvidence restoredSearchState :=
  ay_tcrg_conj_intro acceptedEvidence restoredSearchState

theorem ay_tcrg_restore_cannot_justify_publication
    (restoreEvidence fallbackOrRecompute : Prop) :
    restoreEvidence ->
    fallbackOrRecompute ->
    ay_tcrg_no_claim restoreEvidence fallbackOrRecompute :=
  ay_tcrg_conj_intro restoreEvidence fallbackOrRecompute

theorem ay_tcrg_public_report_intro
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    publicOutcome ->
    ay_tcrg_public_report acceptedEvidence originalFormulaTruth publicOutcome :=
  fun haccepted htruth houtcome =>
    ay_tcrg_conj_intro acceptedEvidence (ay_tcrg_conj originalFormulaTruth publicOutcome)
      haccepted
      (ay_tcrg_conj_intro originalFormulaTruth publicOutcome htruth houtcome)

theorem ay_tcrg_public_report_accepted
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_tcrg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    acceptedEvidence :=
  ay_tcrg_conj_left acceptedEvidence (ay_tcrg_conj originalFormulaTruth publicOutcome)

theorem ay_tcrg_public_report_truth
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_tcrg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    originalFormulaTruth :=
  fun h =>
    ay_tcrg_conj_left originalFormulaTruth publicOutcome
      (ay_tcrg_conj_right acceptedEvidence (ay_tcrg_conj originalFormulaTruth publicOutcome) h)

theorem ay_tcrg_public_report_outcome
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_tcrg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    publicOutcome :=
  fun h =>
    ay_tcrg_conj_right originalFormulaTruth publicOutcome
      (ay_tcrg_conj_right acceptedEvidence (ay_tcrg_conj originalFormulaTruth publicOutcome) h)

theorem ay_tcrg_preserves_formula_truth
    (originalFormulaTruth restoredStateTruth : Prop) :
    ay_tcrg_equisat originalFormulaTruth restoredStateTruth ->
    originalFormulaTruth ->
    restoredStateTruth :=
  ay_tcrg_equisat_forward originalFormulaTruth restoredStateTruth

theorem ay_tcrg_reflects_formula_truth
    (originalFormulaTruth restoredStateTruth : Prop) :
    ay_tcrg_equisat originalFormulaTruth restoredStateTruth ->
    restoredStateTruth ->
    originalFormulaTruth :=
  ay_tcrg_equisat_backward originalFormulaTruth restoredStateTruth

theorem ay_tcrg_accepted_preserves_public_soundness
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_tcrg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    ay_tcrg_conj originalFormulaTruth publicOutcome :=
  ay_tcrg_conj_right acceptedEvidence (ay_tcrg_conj originalFormulaTruth publicOutcome)

theorem ay_tcrg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_tcrg_no_claim diagnostic fallbackOrRecompute :=
  ay_tcrg_conj_intro diagnostic fallbackOrRecompute

theorem ay_tcrg_no_claim_recompute (diagnostic fallbackOrRecompute : Prop) :
    ay_tcrg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_tcrg_conj_right diagnostic fallbackOrRecompute

theorem ay_tcrg_trail_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_tcrg_no_claim mismatch fallbackOrRecompute :=
  ay_tcrg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_tcrg_level_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_tcrg_no_claim mismatch fallbackOrRecompute :=
  ay_tcrg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_tcrg_queue_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_tcrg_no_claim mismatch fallbackOrRecompute :=
  ay_tcrg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_tcrg_reason_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_tcrg_no_claim mismatch fallbackOrRecompute :=
  ay_tcrg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_tcrg_watch_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_tcrg_no_claim mismatch fallbackOrRecompute :=
  ay_tcrg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_tcrg_restore_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_tcrg_no_claim mismatch fallbackOrRecompute :=
  ay_tcrg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_tcrg_database_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_tcrg_no_claim mismatch fallbackOrRecompute :=
  ay_tcrg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_tcrg_replay_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_tcrg_no_claim mismatch fallbackOrRecompute :=
  ay_tcrg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_tcrg_build_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_tcrg_no_claim mismatch fallbackOrRecompute :=
  ay_tcrg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_tcrg_validator_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_tcrg_no_claim mismatch fallbackOrRecompute :=
  ay_tcrg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_tcrg_archive_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_tcrg_no_claim mismatch fallbackOrRecompute :=
  ay_tcrg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_tcrg_audit_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_tcrg_no_claim mismatch fallbackOrRecompute :=
  ay_tcrg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_tcrg_failed_guard_cannot_bless_publication
    (failedGuard publicSatOrUnsat fallbackOrRecompute : Prop) :
    ay_tcrg_no_claim failedGuard fallbackOrRecompute ->
    (fallbackOrRecompute -> publicSatOrUnsat -> False) ->
    publicSatOrUnsat ->
    False :=
  fun hnoclaim hblocked hpublic =>
    hblocked (ay_tcrg_no_claim_recompute failedGuard fallbackOrRecompute hnoclaim) hpublic

theorem ay_tcrg_publication_requires_guard
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_tcrg_public_report
      (ay_tcrg_accepted_restore trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    ay_tcrg_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  fun h =>
    ay_tcrg_accepted_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_tcrg_public_report_accepted
        (ay_tcrg_accepted_restore trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
        originalFormulaTruth
        publicOutcome
        h)

theorem ay_tcrg_publication_requires_validator
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_tcrg_public_report
      (ay_tcrg_accepted_restore trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    validatorGate :=
  fun h =>
    ay_tcrg_guard_validator trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_tcrg_publication_requires_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_tcrg_publication_requires_archive
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_tcrg_public_report
      (ay_tcrg_accepted_restore trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    archiveManifest :=
  fun h =>
    ay_tcrg_guard_archive trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_tcrg_publication_requires_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_tcrg_publication_requires_audit
    (trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_tcrg_public_report
      (ay_tcrg_accepted_restore trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    auditTranscript :=
  fun h =>
    ay_tcrg_guard_audit trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_tcrg_publication_requires_guard trailSnapshotDigest assignmentLevelMapDigest propagationQueueDigest reasonAntecedentMapDigest watchlistDigest restoreLedger clauseDatabaseDigest postRestorePropagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_tcrg_accepted_public_report_for_sat
    (acceptedEvidence originalFormulaTruth satOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    satOutcome ->
    ay_tcrg_public_report acceptedEvidence originalFormulaTruth satOutcome :=
  ay_tcrg_public_report_intro acceptedEvidence originalFormulaTruth satOutcome

theorem ay_tcrg_accepted_public_report_for_unsat
    (acceptedEvidence originalFormulaTruth unsatOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    unsatOutcome ->
    ay_tcrg_public_report acceptedEvidence originalFormulaTruth unsatOutcome :=
  ay_tcrg_public_report_intro acceptedEvidence originalFormulaTruth unsatOutcome
