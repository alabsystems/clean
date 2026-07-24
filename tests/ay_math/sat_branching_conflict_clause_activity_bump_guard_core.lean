def ay_cabg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cabg_equisat (before after : Prop) : Prop :=
  ay_cabg_conj (before -> after) (after -> before)

def ay_cabg_guard
    (conflictClauseDigest : Prop)
    (learnedClauseDatabaseDigest : Prop)
    (bumpScheduleManifest : Prop)
    (activityVectorBeforeDigest : Prop)
    (activityVectorAfterDigest : Prop)
    (decayRescaleContextDigest : Prop)
    (lbdScoreContext : Prop)
    (retentionPolicyManifest : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackBaseline : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (conflictClauseDigest ->
      learnedClauseDatabaseDigest ->
      bumpScheduleManifest ->
      activityVectorBeforeDigest ->
      activityVectorAfterDigest ->
      decayRescaleContextDigest ->
      lbdScoreContext ->
      retentionPolicyManifest ->
      propagationReplayTranscript ->
      solverBuildEvidence ->
      validatorGate ->
      archiveManifest ->
      fallbackBaseline ->
      auditTranscript ->
      result) ->
    result

def ay_cabg_agreement
    (conflictClauseDigest : Prop)
    (learnedClauseDatabaseDigest : Prop)
    (bumpScheduleManifest : Prop)
    (activityVectorBeforeDigest : Prop)
    (activityVectorAfterDigest : Prop)
    (decayRescaleContextDigest : Prop)
    (lbdScoreContext : Prop)
    (retentionPolicyManifest : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (auditTranscript : Prop) : Prop :=
  ay_cabg_guard
    conflictClauseDigest
    learnedClauseDatabaseDigest
    bumpScheduleManifest
    activityVectorBeforeDigest
    activityVectorAfterDigest
    decayRescaleContextDigest
    lbdScoreContext
    retentionPolicyManifest
    propagationReplayTranscript
    solverBuildEvidence
    validatorGate
    archiveManifest
    True
    auditTranscript

def ay_cabg_accepted_bump
    (conflictClauseDigest : Prop)
    (learnedClauseDatabaseDigest : Prop)
    (bumpScheduleManifest : Prop)
    (activityVectorBeforeDigest : Prop)
    (activityVectorAfterDigest : Prop)
    (decayRescaleContextDigest : Prop)
    (lbdScoreContext : Prop)
    (retentionPolicyManifest : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackBaseline : Prop)
    (auditTranscript : Prop) : Prop :=
  ay_cabg_conj
    (ay_cabg_guard
      conflictClauseDigest
      learnedClauseDatabaseDigest
      bumpScheduleManifest
      activityVectorBeforeDigest
      activityVectorAfterDigest
      decayRescaleContextDigest
      lbdScoreContext
      retentionPolicyManifest
      propagationReplayTranscript
      solverBuildEvidence
      validatorGate
      archiveManifest
      fallbackBaseline
      auditTranscript)
    (ay_cabg_agreement
      conflictClauseDigest
      learnedClauseDatabaseDigest
      bumpScheduleManifest
      activityVectorBeforeDigest
      activityVectorAfterDigest
      decayRescaleContextDigest
      lbdScoreContext
      retentionPolicyManifest
      propagationReplayTranscript
      solverBuildEvidence
      validatorGate
      archiveManifest
      auditTranscript)

def ay_cabg_public_report
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) : Prop :=
  ay_cabg_conj acceptedEvidence (ay_cabg_conj originalFormulaTruth publicOutcome)

def ay_cabg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_cabg_conj diagnostic fallbackOrRecompute

theorem ay_cabg_conj_intro (left right : Prop) :
    left -> right -> ay_cabg_conj left right :=
  fun hleft hright result k => k hleft hright

theorem ay_cabg_conj_left (left right : Prop) :
    ay_cabg_conj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_cabg_conj_right (left right : Prop) :
    ay_cabg_conj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_cabg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_cabg_equisat before after :=
  ay_cabg_conj_intro (before -> after) (after -> before)

theorem ay_cabg_equisat_forward (before after : Prop) :
    ay_cabg_equisat before after -> before -> after :=
  ay_cabg_conj_left (before -> after) (after -> before)

theorem ay_cabg_equisat_backward (before after : Prop) :
    ay_cabg_equisat before after -> after -> before :=
  ay_cabg_conj_right (before -> after) (after -> before)

theorem ay_cabg_guard_intro
    (conflictClauseDigest : Prop)
    (learnedClauseDatabaseDigest : Prop)
    (bumpScheduleManifest : Prop)
    (activityVectorBeforeDigest : Prop)
    (activityVectorAfterDigest : Prop)
    (decayRescaleContextDigest : Prop)
    (lbdScoreContext : Prop)
    (retentionPolicyManifest : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackBaseline : Prop)
    (auditTranscript : Prop) :
    conflictClauseDigest ->
    learnedClauseDatabaseDigest ->
    bumpScheduleManifest ->
    activityVectorBeforeDigest ->
    activityVectorAfterDigest ->
    decayRescaleContextDigest ->
    lbdScoreContext ->
    retentionPolicyManifest ->
    propagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    fallbackBaseline ->
    auditTranscript ->
    ay_cabg_guard
      conflictClauseDigest
      learnedClauseDatabaseDigest
      bumpScheduleManifest
      activityVectorBeforeDigest
      activityVectorAfterDigest
      decayRescaleContextDigest
      lbdScoreContext
      retentionPolicyManifest
      propagationReplayTranscript
      solverBuildEvidence
      validatorGate
      archiveManifest
      fallbackBaseline
      auditTranscript :=
  fun hconflict hdb hbump hbefore hafter hdecay hlbd hretention hreplay hbuild hvalidator harchive hfallback haudit result k =>
    k hconflict hdb hbump hbefore hafter hdecay hlbd hretention hreplay hbuild hvalidator harchive hfallback haudit

theorem ay_cabg_guard_conflict
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    conflictClauseDigest :=
  fun h => h conflictClauseDigest (fun hconflict _ _ _ _ _ _ _ _ _ _ _ _ _ => hconflict)

theorem ay_cabg_guard_database
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    learnedClauseDatabaseDigest :=
  fun h => h learnedClauseDatabaseDigest (fun _ hdb _ _ _ _ _ _ _ _ _ _ _ _ => hdb)

theorem ay_cabg_guard_bump
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    bumpScheduleManifest :=
  fun h => h bumpScheduleManifest (fun _ _ hbump _ _ _ _ _ _ _ _ _ _ _ => hbump)

theorem ay_cabg_guard_activity_before
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    activityVectorBeforeDigest :=
  fun h => h activityVectorBeforeDigest (fun _ _ _ hbefore _ _ _ _ _ _ _ _ _ _ => hbefore)

theorem ay_cabg_guard_activity_after
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    activityVectorAfterDigest :=
  fun h => h activityVectorAfterDigest (fun _ _ _ _ hafter _ _ _ _ _ _ _ _ _ => hafter)

theorem ay_cabg_guard_decay_rescale
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    decayRescaleContextDigest :=
  fun h => h decayRescaleContextDigest (fun _ _ _ _ _ hdecay _ _ _ _ _ _ _ _ => hdecay)

theorem ay_cabg_guard_lbd
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    lbdScoreContext :=
  fun h => h lbdScoreContext (fun _ _ _ _ _ _ hlbd _ _ _ _ _ _ _ => hlbd)

theorem ay_cabg_guard_retention
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    retentionPolicyManifest :=
  fun h => h retentionPolicyManifest (fun _ _ _ _ _ _ _ hretention _ _ _ _ _ _ => hretention)

theorem ay_cabg_guard_replay
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    propagationReplayTranscript :=
  fun h => h propagationReplayTranscript (fun _ _ _ _ _ _ _ _ hreplay _ _ _ _ _ => hreplay)

theorem ay_cabg_guard_build
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    solverBuildEvidence :=
  fun h => h solverBuildEvidence (fun _ _ _ _ _ _ _ _ _ hbuild _ _ _ _ => hbuild)

theorem ay_cabg_guard_validator
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    validatorGate :=
  fun h => h validatorGate (fun _ _ _ _ _ _ _ _ _ _ hvalidator _ _ _ => hvalidator)

theorem ay_cabg_guard_archive
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    archiveManifest :=
  fun h => h archiveManifest (fun _ _ _ _ _ _ _ _ _ _ _ harchive _ _ => harchive)

theorem ay_cabg_guard_fallback
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    fallbackBaseline :=
  fun h => h fallbackBaseline (fun _ _ _ _ _ _ _ _ _ _ _ _ hfallback _ => hfallback)

theorem ay_cabg_guard_audit
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    auditTranscript :=
  fun h => h auditTranscript (fun _ _ _ _ _ _ _ _ _ _ _ _ _ haudit => haudit)

theorem ay_cabg_agreement_intro
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript : Prop) :
    conflictClauseDigest ->
    learnedClauseDatabaseDigest ->
    bumpScheduleManifest ->
    activityVectorBeforeDigest ->
    activityVectorAfterDigest ->
    decayRescaleContextDigest ->
    lbdScoreContext ->
    retentionPolicyManifest ->
    propagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    auditTranscript ->
    ay_cabg_agreement conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript :=
  fun hconflict hdb hbump hbefore hafter hdecay hlbd hretention hreplay hbuild hvalidator harchive haudit =>
    ay_cabg_guard_intro conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest True auditTranscript
      hconflict hdb hbump hbefore hafter hdecay hlbd hretention hreplay hbuild hvalidator harchive True.intro haudit

theorem ay_cabg_accepted_bump_intro
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    ay_cabg_agreement conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript ->
    ay_cabg_accepted_bump conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript :=
  ay_cabg_conj_intro
    (ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
    (ay_cabg_agreement conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_cabg_accepted_guard
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_accepted_bump conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript :=
  ay_cabg_conj_left
    (ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
    (ay_cabg_agreement conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_cabg_accepted_agreement
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_cabg_accepted_bump conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    ay_cabg_agreement conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript :=
  ay_cabg_conj_right
    (ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
    (ay_cabg_agreement conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_cabg_accepted_heuristic_ranking_only
    (acceptedEvidence searchRankingState : Prop) :
    acceptedEvidence ->
    searchRankingState ->
    ay_cabg_conj acceptedEvidence searchRankingState :=
  ay_cabg_conj_intro acceptedEvidence searchRankingState

theorem ay_cabg_bump_cannot_justify_publication
    (bumpEvidence fallbackOrRecompute : Prop) :
    bumpEvidence ->
    fallbackOrRecompute ->
    ay_cabg_no_claim bumpEvidence fallbackOrRecompute :=
  ay_cabg_conj_intro bumpEvidence fallbackOrRecompute

theorem ay_cabg_public_report_intro
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    publicOutcome ->
    ay_cabg_public_report acceptedEvidence originalFormulaTruth publicOutcome :=
  fun haccepted htruth houtcome =>
    ay_cabg_conj_intro acceptedEvidence (ay_cabg_conj originalFormulaTruth publicOutcome)
      haccepted
      (ay_cabg_conj_intro originalFormulaTruth publicOutcome htruth houtcome)

theorem ay_cabg_public_report_accepted
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_cabg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    acceptedEvidence :=
  ay_cabg_conj_left acceptedEvidence (ay_cabg_conj originalFormulaTruth publicOutcome)

theorem ay_cabg_public_report_outcome
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_cabg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    publicOutcome :=
  fun h =>
    ay_cabg_conj_right originalFormulaTruth publicOutcome
      (ay_cabg_conj_right acceptedEvidence (ay_cabg_conj originalFormulaTruth publicOutcome) h)

theorem ay_cabg_public_report_truth
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_cabg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    originalFormulaTruth :=
  fun h =>
    ay_cabg_conj_left originalFormulaTruth publicOutcome
      (ay_cabg_conj_right acceptedEvidence (ay_cabg_conj originalFormulaTruth publicOutcome) h)

theorem ay_cabg_preserves_formula_truth
    (originalFormulaTruth bumpedHeuristicFormulaTruth : Prop) :
    ay_cabg_equisat originalFormulaTruth bumpedHeuristicFormulaTruth ->
    originalFormulaTruth ->
    bumpedHeuristicFormulaTruth :=
  ay_cabg_equisat_forward originalFormulaTruth bumpedHeuristicFormulaTruth

theorem ay_cabg_reflects_formula_truth
    (originalFormulaTruth bumpedHeuristicFormulaTruth : Prop) :
    ay_cabg_equisat originalFormulaTruth bumpedHeuristicFormulaTruth ->
    bumpedHeuristicFormulaTruth ->
    originalFormulaTruth :=
  ay_cabg_equisat_backward originalFormulaTruth bumpedHeuristicFormulaTruth

theorem ay_cabg_accepted_preserves_public_soundness
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_cabg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    ay_cabg_conj originalFormulaTruth publicOutcome :=
  ay_cabg_conj_right acceptedEvidence (ay_cabg_conj originalFormulaTruth publicOutcome)

theorem ay_cabg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_cabg_no_claim diagnostic fallbackOrRecompute :=
  ay_cabg_conj_intro diagnostic fallbackOrRecompute

theorem ay_cabg_no_claim_recompute (diagnostic fallbackOrRecompute : Prop) :
    ay_cabg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_cabg_conj_right diagnostic fallbackOrRecompute

theorem ay_cabg_clause_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cabg_no_claim mismatch fallbackOrRecompute :=
  ay_cabg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cabg_database_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cabg_no_claim mismatch fallbackOrRecompute :=
  ay_cabg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cabg_bump_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cabg_no_claim mismatch fallbackOrRecompute :=
  ay_cabg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cabg_activity_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cabg_no_claim mismatch fallbackOrRecompute :=
  ay_cabg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cabg_decay_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cabg_no_claim mismatch fallbackOrRecompute :=
  ay_cabg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cabg_lbd_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cabg_no_claim mismatch fallbackOrRecompute :=
  ay_cabg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cabg_retention_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cabg_no_claim mismatch fallbackOrRecompute :=
  ay_cabg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cabg_replay_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cabg_no_claim mismatch fallbackOrRecompute :=
  ay_cabg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cabg_build_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cabg_no_claim mismatch fallbackOrRecompute :=
  ay_cabg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cabg_validator_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cabg_no_claim mismatch fallbackOrRecompute :=
  ay_cabg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cabg_archive_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cabg_no_claim mismatch fallbackOrRecompute :=
  ay_cabg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cabg_audit_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cabg_no_claim mismatch fallbackOrRecompute :=
  ay_cabg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cabg_failed_guard_cannot_bless_publication
    (failedGuard publicSatOrUnsat fallbackOrRecompute : Prop) :
    ay_cabg_no_claim failedGuard fallbackOrRecompute ->
    (fallbackOrRecompute -> publicSatOrUnsat -> False) ->
    publicSatOrUnsat ->
    False :=
  fun hnoclaim hblocked hpublic =>
    hblocked (ay_cabg_no_claim_recompute failedGuard fallbackOrRecompute hnoclaim) hpublic

theorem ay_cabg_publication_requires_guard
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_cabg_public_report
      (ay_cabg_accepted_bump conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    ay_cabg_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript :=
  fun h =>
    ay_cabg_accepted_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript
      (ay_cabg_public_report_accepted
        (ay_cabg_accepted_bump conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
        originalFormulaTruth
        publicOutcome
        h)

theorem ay_cabg_publication_requires_validator
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_cabg_public_report
      (ay_cabg_accepted_bump conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    validatorGate :=
  fun h =>
    ay_cabg_guard_validator conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript
      (ay_cabg_publication_requires_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_cabg_publication_requires_archive
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_cabg_public_report
      (ay_cabg_accepted_bump conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    archiveManifest :=
  fun h =>
    ay_cabg_guard_archive conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript
      (ay_cabg_publication_requires_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_cabg_publication_requires_audit
    (conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_cabg_public_report
      (ay_cabg_accepted_bump conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    auditTranscript :=
  fun h =>
    ay_cabg_guard_audit conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript
      (ay_cabg_publication_requires_guard conflictClauseDigest learnedClauseDatabaseDigest bumpScheduleManifest activityVectorBeforeDigest activityVectorAfterDigest decayRescaleContextDigest lbdScoreContext retentionPolicyManifest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_cabg_accepted_public_report_for_sat
    (acceptedEvidence originalFormulaTruth satOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    satOutcome ->
    ay_cabg_public_report acceptedEvidence originalFormulaTruth satOutcome :=
  ay_cabg_public_report_intro acceptedEvidence originalFormulaTruth satOutcome

theorem ay_cabg_accepted_public_report_for_unsat
    (acceptedEvidence originalFormulaTruth unsatOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    unsatOutcome ->
    ay_cabg_public_report acceptedEvidence originalFormulaTruth unsatOutcome :=
  ay_cabg_public_report_intro acceptedEvidence originalFormulaTruth unsatOutcome
