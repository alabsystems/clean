def ay_dsug_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_dsug_equisat (before after : Prop) : Prop :=
  ay_dsug_conj (before -> after) (after -> before)

def ay_dsug_guard
    (decisionStackBeforeDigest : Prop)
    (decisionStackAfterDigest : Prop)
    (undoLedger : Prop)
    (decisionLevelMapDigest : Prop)
    (assignmentTrailDigest : Prop)
    (reasonMapDigest : Prop)
    (propagationQueueDigest : Prop)
    (watchedLiteralDigest : Prop)
    (clauseDatabaseDigest : Prop)
    (postUndoReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackNoClaimPath : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (decisionStackBeforeDigest ->
      decisionStackAfterDigest ->
      undoLedger ->
      decisionLevelMapDigest ->
      assignmentTrailDigest ->
      reasonMapDigest ->
      propagationQueueDigest ->
      watchedLiteralDigest ->
      clauseDatabaseDigest ->
      postUndoReplayTranscript ->
      solverBuildEvidence ->
      validatorGate ->
      archiveManifest ->
      fallbackNoClaimPath ->
      auditTranscript ->
      result) ->
    result

def ay_dsug_agreement
    (decisionStackBeforeDigest : Prop)
    (decisionStackAfterDigest : Prop)
    (undoLedger : Prop)
    (decisionLevelMapDigest : Prop)
    (assignmentTrailDigest : Prop)
    (reasonMapDigest : Prop)
    (propagationQueueDigest : Prop)
    (watchedLiteralDigest : Prop)
    (clauseDatabaseDigest : Prop)
    (postUndoReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (auditTranscript : Prop) : Prop :=
  ay_dsug_guard
    decisionStackBeforeDigest
    decisionStackAfterDigest
    undoLedger
    decisionLevelMapDigest
    assignmentTrailDigest
    reasonMapDigest
    propagationQueueDigest
    watchedLiteralDigest
    clauseDatabaseDigest
    postUndoReplayTranscript
    solverBuildEvidence
    validatorGate
    archiveManifest
    True
    auditTranscript

def ay_dsug_accepted_undo
    (decisionStackBeforeDigest : Prop)
    (decisionStackAfterDigest : Prop)
    (undoLedger : Prop)
    (decisionLevelMapDigest : Prop)
    (assignmentTrailDigest : Prop)
    (reasonMapDigest : Prop)
    (propagationQueueDigest : Prop)
    (watchedLiteralDigest : Prop)
    (clauseDatabaseDigest : Prop)
    (postUndoReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackNoClaimPath : Prop)
    (auditTranscript : Prop) : Prop :=
  ay_dsug_conj
    (ay_dsug_guard
      decisionStackBeforeDigest
      decisionStackAfterDigest
      undoLedger
      decisionLevelMapDigest
      assignmentTrailDigest
      reasonMapDigest
      propagationQueueDigest
      watchedLiteralDigest
      clauseDatabaseDigest
      postUndoReplayTranscript
      solverBuildEvidence
      validatorGate
      archiveManifest
      fallbackNoClaimPath
      auditTranscript)
    (ay_dsug_agreement
      decisionStackBeforeDigest
      decisionStackAfterDigest
      undoLedger
      decisionLevelMapDigest
      assignmentTrailDigest
      reasonMapDigest
      propagationQueueDigest
      watchedLiteralDigest
      clauseDatabaseDigest
      postUndoReplayTranscript
      solverBuildEvidence
      validatorGate
      archiveManifest
      auditTranscript)

def ay_dsug_public_report
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) : Prop :=
  ay_dsug_conj acceptedEvidence (ay_dsug_conj originalFormulaTruth publicOutcome)

def ay_dsug_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_dsug_conj diagnostic fallbackOrRecompute

theorem ay_dsug_conj_intro (left right : Prop) :
    left -> right -> ay_dsug_conj left right :=
  fun hleft hright result k => k hleft hright

theorem ay_dsug_conj_left (left right : Prop) :
    ay_dsug_conj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_dsug_conj_right (left right : Prop) :
    ay_dsug_conj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_dsug_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_dsug_equisat before after :=
  ay_dsug_conj_intro (before -> after) (after -> before)

theorem ay_dsug_equisat_forward (before after : Prop) :
    ay_dsug_equisat before after -> before -> after :=
  ay_dsug_conj_left (before -> after) (after -> before)

theorem ay_dsug_equisat_backward (before after : Prop) :
    ay_dsug_equisat before after -> after -> before :=
  ay_dsug_conj_right (before -> after) (after -> before)

theorem ay_dsug_guard_intro
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    decisionStackBeforeDigest ->
    decisionStackAfterDigest ->
    undoLedger ->
    decisionLevelMapDigest ->
    assignmentTrailDigest ->
    reasonMapDigest ->
    propagationQueueDigest ->
    watchedLiteralDigest ->
    clauseDatabaseDigest ->
    postUndoReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    fallbackNoClaimPath ->
    auditTranscript ->
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  fun hbefore hafter hundo hlevel htrail hreason hqueue hwatch hdb hreplay hbuild hvalidator harchive hfallback haudit result k =>
    k hbefore hafter hundo hlevel htrail hreason hqueue hwatch hdb hreplay hbuild hvalidator harchive hfallback haudit

theorem ay_dsug_guard_stack_before
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    decisionStackBeforeDigest :=
  fun h => h decisionStackBeforeDigest (fun hbefore _ _ _ _ _ _ _ _ _ _ _ _ _ _ => hbefore)

theorem ay_dsug_guard_stack_after
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    decisionStackAfterDigest :=
  fun h => h decisionStackAfterDigest (fun _ hafter _ _ _ _ _ _ _ _ _ _ _ _ _ => hafter)

theorem ay_dsug_guard_undo
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    undoLedger :=
  fun h => h undoLedger (fun _ _ hundo _ _ _ _ _ _ _ _ _ _ _ _ => hundo)

theorem ay_dsug_guard_level
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    decisionLevelMapDigest :=
  fun h => h decisionLevelMapDigest (fun _ _ _ hlevel _ _ _ _ _ _ _ _ _ _ _ => hlevel)

theorem ay_dsug_guard_trail
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    assignmentTrailDigest :=
  fun h => h assignmentTrailDigest (fun _ _ _ _ htrail _ _ _ _ _ _ _ _ _ _ => htrail)

theorem ay_dsug_guard_reason
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    reasonMapDigest :=
  fun h => h reasonMapDigest (fun _ _ _ _ _ hreason _ _ _ _ _ _ _ _ _ => hreason)

theorem ay_dsug_guard_queue
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    propagationQueueDigest :=
  fun h => h propagationQueueDigest (fun _ _ _ _ _ _ hqueue _ _ _ _ _ _ _ _ => hqueue)

theorem ay_dsug_guard_watch
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    watchedLiteralDigest :=
  fun h => h watchedLiteralDigest (fun _ _ _ _ _ _ _ hwatch _ _ _ _ _ _ _ => hwatch)

theorem ay_dsug_guard_database
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    clauseDatabaseDigest :=
  fun h => h clauseDatabaseDigest (fun _ _ _ _ _ _ _ _ hdb _ _ _ _ _ _ => hdb)

theorem ay_dsug_guard_replay
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    postUndoReplayTranscript :=
  fun h => h postUndoReplayTranscript (fun _ _ _ _ _ _ _ _ _ hreplay _ _ _ _ _ => hreplay)

theorem ay_dsug_guard_build
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun h => h solverBuildEvidence (fun _ _ _ _ _ _ _ _ _ _ hbuild _ _ _ _ => hbuild)

theorem ay_dsug_guard_validator
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    validatorGate :=
  fun h => h validatorGate (fun _ _ _ _ _ _ _ _ _ _ _ hvalidator _ _ _ => hvalidator)

theorem ay_dsug_guard_archive
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun h => h archiveManifest (fun _ _ _ _ _ _ _ _ _ _ _ _ harchive _ _ => harchive)

theorem ay_dsug_guard_fallback
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun h => h fallbackNoClaimPath (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hfallback _ => hfallback)

theorem ay_dsug_guard_audit
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun h => h auditTranscript (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ haudit => haudit)

theorem ay_dsug_agreement_intro
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript : Prop) :
    decisionStackBeforeDigest ->
    decisionStackAfterDigest ->
    undoLedger ->
    decisionLevelMapDigest ->
    assignmentTrailDigest ->
    reasonMapDigest ->
    propagationQueueDigest ->
    watchedLiteralDigest ->
    clauseDatabaseDigest ->
    postUndoReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    auditTranscript ->
    ay_dsug_agreement decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript :=
  fun hbefore hafter hundo hlevel htrail hreason hqueue hwatch hdb hreplay hbuild hvalidator harchive haudit =>
    ay_dsug_guard_intro decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest True auditTranscript
      hbefore hafter hundo hlevel htrail hreason hqueue hwatch hdb hreplay hbuild hvalidator harchive True.intro haudit

theorem ay_dsug_accepted_undo_intro
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_dsug_agreement decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript ->
    ay_dsug_accepted_undo decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  ay_dsug_conj_intro
    (ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
    (ay_dsug_agreement decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_dsug_accepted_guard
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_accepted_undo decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  ay_dsug_conj_left
    (ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
    (ay_dsug_agreement decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_dsug_accepted_agreement
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_dsug_accepted_undo decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_dsug_agreement decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript :=
  ay_dsug_conj_right
    (ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
    (ay_dsug_agreement decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_dsug_undo_is_search_state_only
    (acceptedEvidence undoSearchState : Prop) :
    acceptedEvidence ->
    undoSearchState ->
    ay_dsug_conj acceptedEvidence undoSearchState :=
  ay_dsug_conj_intro acceptedEvidence undoSearchState

theorem ay_dsug_undo_cannot_justify_publication
    (undoEvidence fallbackOrRecompute : Prop) :
    undoEvidence ->
    fallbackOrRecompute ->
    ay_dsug_no_claim undoEvidence fallbackOrRecompute :=
  ay_dsug_conj_intro undoEvidence fallbackOrRecompute

theorem ay_dsug_public_report_intro
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    publicOutcome ->
    ay_dsug_public_report acceptedEvidence originalFormulaTruth publicOutcome :=
  fun haccepted htruth houtcome =>
    ay_dsug_conj_intro acceptedEvidence (ay_dsug_conj originalFormulaTruth publicOutcome)
      haccepted
      (ay_dsug_conj_intro originalFormulaTruth publicOutcome htruth houtcome)

theorem ay_dsug_public_report_accepted
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_dsug_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    acceptedEvidence :=
  ay_dsug_conj_left acceptedEvidence (ay_dsug_conj originalFormulaTruth publicOutcome)

theorem ay_dsug_public_report_truth
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_dsug_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    originalFormulaTruth :=
  fun h =>
    ay_dsug_conj_left originalFormulaTruth publicOutcome
      (ay_dsug_conj_right acceptedEvidence (ay_dsug_conj originalFormulaTruth publicOutcome) h)

theorem ay_dsug_public_report_outcome
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_dsug_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    publicOutcome :=
  fun h =>
    ay_dsug_conj_right originalFormulaTruth publicOutcome
      (ay_dsug_conj_right acceptedEvidence (ay_dsug_conj originalFormulaTruth publicOutcome) h)

theorem ay_dsug_preserves_formula_truth
    (originalFormulaTruth undoneStateTruth : Prop) :
    ay_dsug_equisat originalFormulaTruth undoneStateTruth ->
    originalFormulaTruth ->
    undoneStateTruth :=
  ay_dsug_equisat_forward originalFormulaTruth undoneStateTruth

theorem ay_dsug_reflects_formula_truth
    (originalFormulaTruth undoneStateTruth : Prop) :
    ay_dsug_equisat originalFormulaTruth undoneStateTruth ->
    undoneStateTruth ->
    originalFormulaTruth :=
  ay_dsug_equisat_backward originalFormulaTruth undoneStateTruth

theorem ay_dsug_accepted_preserves_public_soundness
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_dsug_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    ay_dsug_conj originalFormulaTruth publicOutcome :=
  ay_dsug_conj_right acceptedEvidence (ay_dsug_conj originalFormulaTruth publicOutcome)

theorem ay_dsug_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_dsug_no_claim diagnostic fallbackOrRecompute :=
  ay_dsug_conj_intro diagnostic fallbackOrRecompute

theorem ay_dsug_no_claim_recompute (diagnostic fallbackOrRecompute : Prop) :
    ay_dsug_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_dsug_conj_right diagnostic fallbackOrRecompute

theorem ay_dsug_stack_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dsug_no_claim mismatch fallbackOrRecompute :=
  ay_dsug_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dsug_undo_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dsug_no_claim mismatch fallbackOrRecompute :=
  ay_dsug_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dsug_level_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dsug_no_claim mismatch fallbackOrRecompute :=
  ay_dsug_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dsug_trail_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dsug_no_claim mismatch fallbackOrRecompute :=
  ay_dsug_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dsug_reason_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dsug_no_claim mismatch fallbackOrRecompute :=
  ay_dsug_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dsug_queue_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dsug_no_claim mismatch fallbackOrRecompute :=
  ay_dsug_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dsug_watch_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dsug_no_claim mismatch fallbackOrRecompute :=
  ay_dsug_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dsug_database_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dsug_no_claim mismatch fallbackOrRecompute :=
  ay_dsug_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dsug_replay_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dsug_no_claim mismatch fallbackOrRecompute :=
  ay_dsug_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dsug_build_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dsug_no_claim mismatch fallbackOrRecompute :=
  ay_dsug_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dsug_validator_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dsug_no_claim mismatch fallbackOrRecompute :=
  ay_dsug_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dsug_archive_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dsug_no_claim mismatch fallbackOrRecompute :=
  ay_dsug_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dsug_audit_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dsug_no_claim mismatch fallbackOrRecompute :=
  ay_dsug_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dsug_failed_guard_cannot_bless_publication
    (failedGuard publicSatOrUnsat fallbackOrRecompute : Prop) :
    ay_dsug_no_claim failedGuard fallbackOrRecompute ->
    (fallbackOrRecompute -> publicSatOrUnsat -> False) ->
    publicSatOrUnsat ->
    False :=
  fun hnoclaim hblocked hpublic =>
    hblocked (ay_dsug_no_claim_recompute failedGuard fallbackOrRecompute hnoclaim) hpublic

theorem ay_dsug_publication_requires_guard
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_dsug_public_report
      (ay_dsug_accepted_undo decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    ay_dsug_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  fun h =>
    ay_dsug_accepted_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_dsug_public_report_accepted
        (ay_dsug_accepted_undo decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
        originalFormulaTruth
        publicOutcome
        h)

theorem ay_dsug_publication_requires_validator
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_dsug_public_report
      (ay_dsug_accepted_undo decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    validatorGate :=
  fun h =>
    ay_dsug_guard_validator decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_dsug_publication_requires_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_dsug_publication_requires_archive
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_dsug_public_report
      (ay_dsug_accepted_undo decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    archiveManifest :=
  fun h =>
    ay_dsug_guard_archive decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_dsug_publication_requires_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_dsug_publication_requires_audit
    (decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_dsug_public_report
      (ay_dsug_accepted_undo decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    auditTranscript :=
  fun h =>
    ay_dsug_guard_audit decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_dsug_publication_requires_guard decisionStackBeforeDigest decisionStackAfterDigest undoLedger decisionLevelMapDigest assignmentTrailDigest reasonMapDigest propagationQueueDigest watchedLiteralDigest clauseDatabaseDigest postUndoReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_dsug_accepted_public_report_for_sat
    (acceptedEvidence originalFormulaTruth satOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    satOutcome ->
    ay_dsug_public_report acceptedEvidence originalFormulaTruth satOutcome :=
  ay_dsug_public_report_intro acceptedEvidence originalFormulaTruth satOutcome

theorem ay_dsug_accepted_public_report_for_unsat
    (acceptedEvidence originalFormulaTruth unsatOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    unsatOutcome ->
    ay_dsug_public_report acceptedEvidence originalFormulaTruth unsatOutcome :=
  ay_dsug_public_report_intro acceptedEvidence originalFormulaTruth unsatOutcome
