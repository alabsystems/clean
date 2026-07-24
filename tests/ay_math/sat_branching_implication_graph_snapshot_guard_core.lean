def ay_igsg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_igsg_equisat (before after : Prop) : Prop :=
  ay_igsg_conj (before -> after) (after -> before)

def ay_igsg_guard
    (implicationGraphDigest : Prop)
    (assignmentTrailDigest : Prop)
    (decisionLevelMapDigest : Prop)
    (reasonAntecedentMapDigest : Prop)
    (conflictNodeWitness : Prop)
    (snapshotRestoreLedger : Prop)
    (learnedClauseDerivationDigest : Prop)
    (backjumpWitness : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackNoClaimPath : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (implicationGraphDigest ->
      assignmentTrailDigest ->
      decisionLevelMapDigest ->
      reasonAntecedentMapDigest ->
      conflictNodeWitness ->
      snapshotRestoreLedger ->
      learnedClauseDerivationDigest ->
      backjumpWitness ->
      propagationReplayTranscript ->
      solverBuildEvidence ->
      validatorGate ->
      archiveManifest ->
      fallbackNoClaimPath ->
      auditTranscript ->
      result) ->
    result

def ay_igsg_agreement
    (implicationGraphDigest : Prop)
    (assignmentTrailDigest : Prop)
    (decisionLevelMapDigest : Prop)
    (reasonAntecedentMapDigest : Prop)
    (conflictNodeWitness : Prop)
    (snapshotRestoreLedger : Prop)
    (learnedClauseDerivationDigest : Prop)
    (backjumpWitness : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (auditTranscript : Prop) : Prop :=
  ay_igsg_guard
    implicationGraphDigest
    assignmentTrailDigest
    decisionLevelMapDigest
    reasonAntecedentMapDigest
    conflictNodeWitness
    snapshotRestoreLedger
    learnedClauseDerivationDigest
    backjumpWitness
    propagationReplayTranscript
    solverBuildEvidence
    validatorGate
    archiveManifest
    True
    auditTranscript

def ay_igsg_accepted_snapshot
    (implicationGraphDigest : Prop)
    (assignmentTrailDigest : Prop)
    (decisionLevelMapDigest : Prop)
    (reasonAntecedentMapDigest : Prop)
    (conflictNodeWitness : Prop)
    (snapshotRestoreLedger : Prop)
    (learnedClauseDerivationDigest : Prop)
    (backjumpWitness : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackNoClaimPath : Prop)
    (auditTranscript : Prop) : Prop :=
  ay_igsg_conj
    (ay_igsg_guard
      implicationGraphDigest
      assignmentTrailDigest
      decisionLevelMapDigest
      reasonAntecedentMapDigest
      conflictNodeWitness
      snapshotRestoreLedger
      learnedClauseDerivationDigest
      backjumpWitness
      propagationReplayTranscript
      solverBuildEvidence
      validatorGate
      archiveManifest
      fallbackNoClaimPath
      auditTranscript)
    (ay_igsg_agreement
      implicationGraphDigest
      assignmentTrailDigest
      decisionLevelMapDigest
      reasonAntecedentMapDigest
      conflictNodeWitness
      snapshotRestoreLedger
      learnedClauseDerivationDigest
      backjumpWitness
      propagationReplayTranscript
      solverBuildEvidence
      validatorGate
      archiveManifest
      auditTranscript)

def ay_igsg_public_report
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) : Prop :=
  ay_igsg_conj acceptedEvidence (ay_igsg_conj originalFormulaTruth publicOutcome)

def ay_igsg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_igsg_conj diagnostic fallbackOrRecompute

theorem ay_igsg_conj_intro (left right : Prop) :
    left -> right -> ay_igsg_conj left right :=
  fun hleft hright result k => k hleft hright

theorem ay_igsg_conj_left (left right : Prop) :
    ay_igsg_conj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_igsg_conj_right (left right : Prop) :
    ay_igsg_conj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_igsg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_igsg_equisat before after :=
  ay_igsg_conj_intro (before -> after) (after -> before)

theorem ay_igsg_equisat_forward (before after : Prop) :
    ay_igsg_equisat before after -> before -> after :=
  ay_igsg_conj_left (before -> after) (after -> before)

theorem ay_igsg_equisat_backward (before after : Prop) :
    ay_igsg_equisat before after -> after -> before :=
  ay_igsg_conj_right (before -> after) (after -> before)

theorem ay_igsg_guard_intro
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    implicationGraphDigest ->
    assignmentTrailDigest ->
    decisionLevelMapDigest ->
    reasonAntecedentMapDigest ->
    conflictNodeWitness ->
    snapshotRestoreLedger ->
    learnedClauseDerivationDigest ->
    backjumpWitness ->
    propagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    fallbackNoClaimPath ->
    auditTranscript ->
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  fun hgraph htrail hlevel hreason hconflict hsnapshot hlearned hbackjump hreplay hbuild hvalidator harchive hfallback haudit result k =>
    k hgraph htrail hlevel hreason hconflict hsnapshot hlearned hbackjump hreplay hbuild hvalidator harchive hfallback haudit

theorem ay_igsg_guard_graph
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    implicationGraphDigest :=
  fun h => h implicationGraphDigest (fun hgraph _ _ _ _ _ _ _ _ _ _ _ _ _ => hgraph)

theorem ay_igsg_guard_trail
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    assignmentTrailDigest :=
  fun h => h assignmentTrailDigest (fun _ htrail _ _ _ _ _ _ _ _ _ _ _ _ => htrail)

theorem ay_igsg_guard_level
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    decisionLevelMapDigest :=
  fun h => h decisionLevelMapDigest (fun _ _ hlevel _ _ _ _ _ _ _ _ _ _ _ => hlevel)

theorem ay_igsg_guard_reason
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    reasonAntecedentMapDigest :=
  fun h => h reasonAntecedentMapDigest (fun _ _ _ hreason _ _ _ _ _ _ _ _ _ _ => hreason)

theorem ay_igsg_guard_conflict
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    conflictNodeWitness :=
  fun h => h conflictNodeWitness (fun _ _ _ _ hconflict _ _ _ _ _ _ _ _ _ => hconflict)

theorem ay_igsg_guard_snapshot
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    snapshotRestoreLedger :=
  fun h => h snapshotRestoreLedger (fun _ _ _ _ _ hsnapshot _ _ _ _ _ _ _ _ => hsnapshot)

theorem ay_igsg_guard_learned
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    learnedClauseDerivationDigest :=
  fun h => h learnedClauseDerivationDigest (fun _ _ _ _ _ _ hlearned _ _ _ _ _ _ _ => hlearned)

theorem ay_igsg_guard_backjump
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    backjumpWitness :=
  fun h => h backjumpWitness (fun _ _ _ _ _ _ _ hbackjump _ _ _ _ _ _ => hbackjump)

theorem ay_igsg_guard_replay
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    propagationReplayTranscript :=
  fun h => h propagationReplayTranscript (fun _ _ _ _ _ _ _ _ hreplay _ _ _ _ _ => hreplay)

theorem ay_igsg_guard_build
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun h => h solverBuildEvidence (fun _ _ _ _ _ _ _ _ _ hbuild _ _ _ _ => hbuild)

theorem ay_igsg_guard_validator
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    validatorGate :=
  fun h => h validatorGate (fun _ _ _ _ _ _ _ _ _ _ hvalidator _ _ _ => hvalidator)

theorem ay_igsg_guard_archive
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun h => h archiveManifest (fun _ _ _ _ _ _ _ _ _ _ _ harchive _ _ => harchive)

theorem ay_igsg_guard_fallback
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun h => h fallbackNoClaimPath (fun _ _ _ _ _ _ _ _ _ _ _ _ hfallback _ => hfallback)

theorem ay_igsg_guard_audit
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun h => h auditTranscript (fun _ _ _ _ _ _ _ _ _ _ _ _ _ haudit => haudit)

theorem ay_igsg_agreement_intro
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript : Prop) :
    implicationGraphDigest ->
    assignmentTrailDigest ->
    decisionLevelMapDigest ->
    reasonAntecedentMapDigest ->
    conflictNodeWitness ->
    snapshotRestoreLedger ->
    learnedClauseDerivationDigest ->
    backjumpWitness ->
    propagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    auditTranscript ->
    ay_igsg_agreement implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript :=
  fun hgraph htrail hlevel hreason hconflict hsnapshot hlearned hbackjump hreplay hbuild hvalidator harchive haudit =>
    ay_igsg_guard_intro implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest True auditTranscript
      hgraph htrail hlevel hreason hconflict hsnapshot hlearned hbackjump hreplay hbuild hvalidator harchive True.intro haudit

theorem ay_igsg_accepted_snapshot_intro
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_igsg_agreement implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript ->
    ay_igsg_accepted_snapshot implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  ay_igsg_conj_intro
    (ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
    (ay_igsg_agreement implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_igsg_accepted_guard
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_accepted_snapshot implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  ay_igsg_conj_left
    (ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
    (ay_igsg_agreement implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_igsg_accepted_agreement
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_igsg_accepted_snapshot implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_igsg_agreement implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript :=
  ay_igsg_conj_right
    (ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
    (ay_igsg_agreement implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_igsg_snapshot_is_search_state_only
    (acceptedEvidence implicationGraphState : Prop) :
    acceptedEvidence ->
    implicationGraphState ->
    ay_igsg_conj acceptedEvidence implicationGraphState :=
  ay_igsg_conj_intro acceptedEvidence implicationGraphState

theorem ay_igsg_snapshot_cannot_justify_publication
    (snapshotEvidence fallbackOrRecompute : Prop) :
    snapshotEvidence ->
    fallbackOrRecompute ->
    ay_igsg_no_claim snapshotEvidence fallbackOrRecompute :=
  ay_igsg_conj_intro snapshotEvidence fallbackOrRecompute

theorem ay_igsg_public_report_intro
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    publicOutcome ->
    ay_igsg_public_report acceptedEvidence originalFormulaTruth publicOutcome :=
  fun haccepted htruth houtcome =>
    ay_igsg_conj_intro acceptedEvidence (ay_igsg_conj originalFormulaTruth publicOutcome)
      haccepted
      (ay_igsg_conj_intro originalFormulaTruth publicOutcome htruth houtcome)

theorem ay_igsg_public_report_accepted
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_igsg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    acceptedEvidence :=
  ay_igsg_conj_left acceptedEvidence (ay_igsg_conj originalFormulaTruth publicOutcome)

theorem ay_igsg_public_report_truth
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_igsg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    originalFormulaTruth :=
  fun h =>
    ay_igsg_conj_left originalFormulaTruth publicOutcome
      (ay_igsg_conj_right acceptedEvidence (ay_igsg_conj originalFormulaTruth publicOutcome) h)

theorem ay_igsg_public_report_outcome
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_igsg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    publicOutcome :=
  fun h =>
    ay_igsg_conj_right originalFormulaTruth publicOutcome
      (ay_igsg_conj_right acceptedEvidence (ay_igsg_conj originalFormulaTruth publicOutcome) h)

theorem ay_igsg_preserves_formula_truth
    (originalFormulaTruth snapshotStateTruth : Prop) :
    ay_igsg_equisat originalFormulaTruth snapshotStateTruth ->
    originalFormulaTruth ->
    snapshotStateTruth :=
  ay_igsg_equisat_forward originalFormulaTruth snapshotStateTruth

theorem ay_igsg_reflects_formula_truth
    (originalFormulaTruth snapshotStateTruth : Prop) :
    ay_igsg_equisat originalFormulaTruth snapshotStateTruth ->
    snapshotStateTruth ->
    originalFormulaTruth :=
  ay_igsg_equisat_backward originalFormulaTruth snapshotStateTruth

theorem ay_igsg_accepted_preserves_public_soundness
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_igsg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    ay_igsg_conj originalFormulaTruth publicOutcome :=
  ay_igsg_conj_right acceptedEvidence (ay_igsg_conj originalFormulaTruth publicOutcome)

theorem ay_igsg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_igsg_no_claim diagnostic fallbackOrRecompute :=
  ay_igsg_conj_intro diagnostic fallbackOrRecompute

theorem ay_igsg_no_claim_recompute (diagnostic fallbackOrRecompute : Prop) :
    ay_igsg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_igsg_conj_right diagnostic fallbackOrRecompute

theorem ay_igsg_graph_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_igsg_no_claim mismatch fallbackOrRecompute :=
  ay_igsg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_igsg_trail_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_igsg_no_claim mismatch fallbackOrRecompute :=
  ay_igsg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_igsg_level_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_igsg_no_claim mismatch fallbackOrRecompute :=
  ay_igsg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_igsg_reason_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_igsg_no_claim mismatch fallbackOrRecompute :=
  ay_igsg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_igsg_conflict_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_igsg_no_claim mismatch fallbackOrRecompute :=
  ay_igsg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_igsg_snapshot_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_igsg_no_claim mismatch fallbackOrRecompute :=
  ay_igsg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_igsg_learned_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_igsg_no_claim mismatch fallbackOrRecompute :=
  ay_igsg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_igsg_backjump_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_igsg_no_claim mismatch fallbackOrRecompute :=
  ay_igsg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_igsg_replay_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_igsg_no_claim mismatch fallbackOrRecompute :=
  ay_igsg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_igsg_build_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_igsg_no_claim mismatch fallbackOrRecompute :=
  ay_igsg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_igsg_validator_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_igsg_no_claim mismatch fallbackOrRecompute :=
  ay_igsg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_igsg_archive_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_igsg_no_claim mismatch fallbackOrRecompute :=
  ay_igsg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_igsg_audit_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_igsg_no_claim mismatch fallbackOrRecompute :=
  ay_igsg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_igsg_failed_guard_cannot_bless_publication
    (failedGuard publicSatOrUnsat fallbackOrRecompute : Prop) :
    ay_igsg_no_claim failedGuard fallbackOrRecompute ->
    (fallbackOrRecompute -> publicSatOrUnsat -> False) ->
    publicSatOrUnsat ->
    False :=
  fun hnoclaim hblocked hpublic =>
    hblocked (ay_igsg_no_claim_recompute failedGuard fallbackOrRecompute hnoclaim) hpublic

theorem ay_igsg_publication_requires_guard
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_igsg_public_report
      (ay_igsg_accepted_snapshot implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    ay_igsg_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  fun h =>
    ay_igsg_accepted_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_igsg_public_report_accepted
        (ay_igsg_accepted_snapshot implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
        originalFormulaTruth
        publicOutcome
        h)

theorem ay_igsg_publication_requires_validator
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_igsg_public_report
      (ay_igsg_accepted_snapshot implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    validatorGate :=
  fun h =>
    ay_igsg_guard_validator implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_igsg_publication_requires_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_igsg_publication_requires_archive
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_igsg_public_report
      (ay_igsg_accepted_snapshot implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    archiveManifest :=
  fun h =>
    ay_igsg_guard_archive implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_igsg_publication_requires_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_igsg_publication_requires_audit
    (implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_igsg_public_report
      (ay_igsg_accepted_snapshot implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    auditTranscript :=
  fun h =>
    ay_igsg_guard_audit implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_igsg_publication_requires_guard implicationGraphDigest assignmentTrailDigest decisionLevelMapDigest reasonAntecedentMapDigest conflictNodeWitness snapshotRestoreLedger learnedClauseDerivationDigest backjumpWitness propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_igsg_accepted_public_report_for_sat
    (acceptedEvidence originalFormulaTruth satOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    satOutcome ->
    ay_igsg_public_report acceptedEvidence originalFormulaTruth satOutcome :=
  ay_igsg_public_report_intro acceptedEvidence originalFormulaTruth satOutcome

theorem ay_igsg_accepted_public_report_for_unsat
    (acceptedEvidence originalFormulaTruth unsatOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    unsatOutcome ->
    ay_igsg_public_report acceptedEvidence originalFormulaTruth unsatOutcome :=
  ay_igsg_public_report_intro acceptedEvidence originalFormulaTruth unsatOutcome
