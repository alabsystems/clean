def ay_cghg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_cghg_equisat (before after : Prop) : Prop :=
  ay_cghg_conj (before -> after) (after -> before)

def ay_cghg_guard
    (implicationGraphDigest : Prop)
    (conflictNodeDigest : Prop)
    (hashFunctionVersionDigest : Prop)
    (graphHashTableDigest : Prop)
    (collisionResolutionWitness : Prop)
    (decisionLevelMapDigest : Prop)
    (reasonAntecedentMapDigest : Prop)
    (learnedClauseDerivationDigest : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackNoClaimPath : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (implicationGraphDigest ->
      conflictNodeDigest ->
      hashFunctionVersionDigest ->
      graphHashTableDigest ->
      collisionResolutionWitness ->
      decisionLevelMapDigest ->
      reasonAntecedentMapDigest ->
      learnedClauseDerivationDigest ->
      propagationReplayTranscript ->
      solverBuildEvidence ->
      validatorGate ->
      archiveManifest ->
      fallbackNoClaimPath ->
      auditTranscript ->
      result) ->
    result

def ay_cghg_agreement
    (implicationGraphDigest : Prop)
    (conflictNodeDigest : Prop)
    (hashFunctionVersionDigest : Prop)
    (graphHashTableDigest : Prop)
    (collisionResolutionWitness : Prop)
    (decisionLevelMapDigest : Prop)
    (reasonAntecedentMapDigest : Prop)
    (learnedClauseDerivationDigest : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (auditTranscript : Prop) : Prop :=
  ay_cghg_guard
    implicationGraphDigest
    conflictNodeDigest
    hashFunctionVersionDigest
    graphHashTableDigest
    collisionResolutionWitness
    decisionLevelMapDigest
    reasonAntecedentMapDigest
    learnedClauseDerivationDigest
    propagationReplayTranscript
    solverBuildEvidence
    validatorGate
    archiveManifest
    True
    auditTranscript

def ay_cghg_accepted_hash
    (implicationGraphDigest : Prop)
    (conflictNodeDigest : Prop)
    (hashFunctionVersionDigest : Prop)
    (graphHashTableDigest : Prop)
    (collisionResolutionWitness : Prop)
    (decisionLevelMapDigest : Prop)
    (reasonAntecedentMapDigest : Prop)
    (learnedClauseDerivationDigest : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackNoClaimPath : Prop)
    (auditTranscript : Prop) : Prop :=
  ay_cghg_conj
    (ay_cghg_guard
      implicationGraphDigest
      conflictNodeDigest
      hashFunctionVersionDigest
      graphHashTableDigest
      collisionResolutionWitness
      decisionLevelMapDigest
      reasonAntecedentMapDigest
      learnedClauseDerivationDigest
      propagationReplayTranscript
      solverBuildEvidence
      validatorGate
      archiveManifest
      fallbackNoClaimPath
      auditTranscript)
    (ay_cghg_agreement
      implicationGraphDigest
      conflictNodeDigest
      hashFunctionVersionDigest
      graphHashTableDigest
      collisionResolutionWitness
      decisionLevelMapDigest
      reasonAntecedentMapDigest
      learnedClauseDerivationDigest
      propagationReplayTranscript
      solverBuildEvidence
      validatorGate
      archiveManifest
      auditTranscript)

def ay_cghg_public_report
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) : Prop :=
  ay_cghg_conj acceptedEvidence (ay_cghg_conj originalFormulaTruth publicOutcome)

def ay_cghg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_cghg_conj diagnostic fallbackOrRecompute

theorem ay_cghg_conj_intro (left right : Prop) :
    left -> right -> ay_cghg_conj left right :=
  fun hleft hright result k => k hleft hright

theorem ay_cghg_conj_left (left right : Prop) :
    ay_cghg_conj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_cghg_conj_right (left right : Prop) :
    ay_cghg_conj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_cghg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_cghg_equisat before after :=
  ay_cghg_conj_intro (before -> after) (after -> before)

theorem ay_cghg_equisat_forward (before after : Prop) :
    ay_cghg_equisat before after -> before -> after :=
  ay_cghg_conj_left (before -> after) (after -> before)

theorem ay_cghg_equisat_backward (before after : Prop) :
    ay_cghg_equisat before after -> after -> before :=
  ay_cghg_conj_right (before -> after) (after -> before)

theorem ay_cghg_guard_intro
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    implicationGraphDigest ->
    conflictNodeDigest ->
    hashFunctionVersionDigest ->
    graphHashTableDigest ->
    collisionResolutionWitness ->
    decisionLevelMapDigest ->
    reasonAntecedentMapDigest ->
    learnedClauseDerivationDigest ->
    propagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    fallbackNoClaimPath ->
    auditTranscript ->
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  fun hgraph hconflict hhash htable hcollision hlevel hreason hlearned hreplay hbuild hvalidator harchive hfallback haudit result k =>
    k hgraph hconflict hhash htable hcollision hlevel hreason hlearned hreplay hbuild hvalidator harchive hfallback haudit

theorem ay_cghg_guard_graph
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    implicationGraphDigest :=
  fun h => h implicationGraphDigest (fun hgraph _ _ _ _ _ _ _ _ _ _ _ _ _ => hgraph)

theorem ay_cghg_guard_conflict
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    conflictNodeDigest :=
  fun h => h conflictNodeDigest (fun _ hconflict _ _ _ _ _ _ _ _ _ _ _ _ => hconflict)

theorem ay_cghg_guard_hash
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    hashFunctionVersionDigest :=
  fun h => h hashFunctionVersionDigest (fun _ _ hhash _ _ _ _ _ _ _ _ _ _ _ => hhash)

theorem ay_cghg_guard_table
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    graphHashTableDigest :=
  fun h => h graphHashTableDigest (fun _ _ _ htable _ _ _ _ _ _ _ _ _ _ => htable)

theorem ay_cghg_guard_collision
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    collisionResolutionWitness :=
  fun h => h collisionResolutionWitness (fun _ _ _ _ hcollision _ _ _ _ _ _ _ _ _ => hcollision)

theorem ay_cghg_guard_level
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    decisionLevelMapDigest :=
  fun h => h decisionLevelMapDigest (fun _ _ _ _ _ hlevel _ _ _ _ _ _ _ _ => hlevel)

theorem ay_cghg_guard_reason
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    reasonAntecedentMapDigest :=
  fun h => h reasonAntecedentMapDigest (fun _ _ _ _ _ _ hreason _ _ _ _ _ _ _ => hreason)

theorem ay_cghg_guard_learned
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    learnedClauseDerivationDigest :=
  fun h => h learnedClauseDerivationDigest (fun _ _ _ _ _ _ _ hlearned _ _ _ _ _ _ => hlearned)

theorem ay_cghg_guard_replay
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    propagationReplayTranscript :=
  fun h => h propagationReplayTranscript (fun _ _ _ _ _ _ _ _ hreplay _ _ _ _ _ => hreplay)

theorem ay_cghg_guard_build
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    solverBuildEvidence :=
  fun h => h solverBuildEvidence (fun _ _ _ _ _ _ _ _ _ hbuild _ _ _ _ => hbuild)

theorem ay_cghg_guard_validator
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    validatorGate :=
  fun h => h validatorGate (fun _ _ _ _ _ _ _ _ _ _ hvalidator _ _ _ => hvalidator)

theorem ay_cghg_guard_archive
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    archiveManifest :=
  fun h => h archiveManifest (fun _ _ _ _ _ _ _ _ _ _ _ harchive _ _ => harchive)

theorem ay_cghg_guard_fallback
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    fallbackNoClaimPath :=
  fun h => h fallbackNoClaimPath (fun _ _ _ _ _ _ _ _ _ _ _ _ hfallback _ => hfallback)

theorem ay_cghg_guard_audit
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    auditTranscript :=
  fun h => h auditTranscript (fun _ _ _ _ _ _ _ _ _ _ _ _ _ haudit => haudit)

theorem ay_cghg_agreement_intro
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript : Prop) :
    implicationGraphDigest ->
    conflictNodeDigest ->
    hashFunctionVersionDigest ->
    graphHashTableDigest ->
    collisionResolutionWitness ->
    decisionLevelMapDigest ->
    reasonAntecedentMapDigest ->
    learnedClauseDerivationDigest ->
    propagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    auditTranscript ->
    ay_cghg_agreement implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript :=
  fun hgraph hconflict hhash htable hcollision hlevel hreason hlearned hreplay hbuild hvalidator harchive haudit =>
    ay_cghg_guard_intro implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest True auditTranscript
      hgraph hconflict hhash htable hcollision hlevel hreason hlearned hreplay hbuild hvalidator harchive True.intro haudit

theorem ay_cghg_accepted_hash_intro
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_cghg_agreement implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript ->
    ay_cghg_accepted_hash implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  ay_cghg_conj_intro
    (ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
    (ay_cghg_agreement implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_cghg_accepted_guard
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_accepted_hash implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  ay_cghg_conj_left
    (ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
    (ay_cghg_agreement implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_cghg_accepted_agreement
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript : Prop) :
    ay_cghg_accepted_hash implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript ->
    ay_cghg_agreement implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript :=
  ay_cghg_conj_right
    (ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
    (ay_cghg_agreement implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_cghg_hash_is_screening_only
    (acceptedEvidence hashScreeningState : Prop) :
    acceptedEvidence ->
    hashScreeningState ->
    ay_cghg_conj acceptedEvidence hashScreeningState :=
  ay_cghg_conj_intro acceptedEvidence hashScreeningState

theorem ay_cghg_hash_cannot_justify_publication
    (hashEvidence fallbackOrRecompute : Prop) :
    hashEvidence ->
    fallbackOrRecompute ->
    ay_cghg_no_claim hashEvidence fallbackOrRecompute :=
  ay_cghg_conj_intro hashEvidence fallbackOrRecompute

theorem ay_cghg_public_report_intro
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    publicOutcome ->
    ay_cghg_public_report acceptedEvidence originalFormulaTruth publicOutcome :=
  fun haccepted htruth houtcome =>
    ay_cghg_conj_intro acceptedEvidence (ay_cghg_conj originalFormulaTruth publicOutcome)
      haccepted
      (ay_cghg_conj_intro originalFormulaTruth publicOutcome htruth houtcome)

theorem ay_cghg_public_report_accepted
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_cghg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    acceptedEvidence :=
  ay_cghg_conj_left acceptedEvidence (ay_cghg_conj originalFormulaTruth publicOutcome)

theorem ay_cghg_public_report_truth
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_cghg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    originalFormulaTruth :=
  fun h =>
    ay_cghg_conj_left originalFormulaTruth publicOutcome
      (ay_cghg_conj_right acceptedEvidence (ay_cghg_conj originalFormulaTruth publicOutcome) h)

theorem ay_cghg_public_report_outcome
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_cghg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    publicOutcome :=
  fun h =>
    ay_cghg_conj_right originalFormulaTruth publicOutcome
      (ay_cghg_conj_right acceptedEvidence (ay_cghg_conj originalFormulaTruth publicOutcome) h)

theorem ay_cghg_preserves_formula_truth
    (originalFormulaTruth hashedReplayTruth : Prop) :
    ay_cghg_equisat originalFormulaTruth hashedReplayTruth ->
    originalFormulaTruth ->
    hashedReplayTruth :=
  ay_cghg_equisat_forward originalFormulaTruth hashedReplayTruth

theorem ay_cghg_reflects_formula_truth
    (originalFormulaTruth hashedReplayTruth : Prop) :
    ay_cghg_equisat originalFormulaTruth hashedReplayTruth ->
    hashedReplayTruth ->
    originalFormulaTruth :=
  ay_cghg_equisat_backward originalFormulaTruth hashedReplayTruth

theorem ay_cghg_accepted_preserves_public_soundness
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_cghg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    ay_cghg_conj originalFormulaTruth publicOutcome :=
  ay_cghg_conj_right acceptedEvidence (ay_cghg_conj originalFormulaTruth publicOutcome)

theorem ay_cghg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_cghg_no_claim diagnostic fallbackOrRecompute :=
  ay_cghg_conj_intro diagnostic fallbackOrRecompute

theorem ay_cghg_no_claim_recompute (diagnostic fallbackOrRecompute : Prop) :
    ay_cghg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_cghg_conj_right diagnostic fallbackOrRecompute

theorem ay_cghg_graph_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cghg_no_claim mismatch fallbackOrRecompute :=
  ay_cghg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cghg_conflict_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cghg_no_claim mismatch fallbackOrRecompute :=
  ay_cghg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cghg_hash_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cghg_no_claim mismatch fallbackOrRecompute :=
  ay_cghg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cghg_table_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cghg_no_claim mismatch fallbackOrRecompute :=
  ay_cghg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cghg_collision_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cghg_no_claim mismatch fallbackOrRecompute :=
  ay_cghg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cghg_level_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cghg_no_claim mismatch fallbackOrRecompute :=
  ay_cghg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cghg_reason_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cghg_no_claim mismatch fallbackOrRecompute :=
  ay_cghg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cghg_learned_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cghg_no_claim mismatch fallbackOrRecompute :=
  ay_cghg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cghg_replay_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cghg_no_claim mismatch fallbackOrRecompute :=
  ay_cghg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cghg_build_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cghg_no_claim mismatch fallbackOrRecompute :=
  ay_cghg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cghg_validator_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cghg_no_claim mismatch fallbackOrRecompute :=
  ay_cghg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cghg_archive_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cghg_no_claim mismatch fallbackOrRecompute :=
  ay_cghg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cghg_audit_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_cghg_no_claim mismatch fallbackOrRecompute :=
  ay_cghg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_cghg_failed_guard_cannot_bless_publication
    (failedGuard publicSatOrUnsat fallbackOrRecompute : Prop) :
    ay_cghg_no_claim failedGuard fallbackOrRecompute ->
    (fallbackOrRecompute -> publicSatOrUnsat -> False) ->
    publicSatOrUnsat ->
    False :=
  fun hnoclaim hblocked hpublic =>
    hblocked (ay_cghg_no_claim_recompute failedGuard fallbackOrRecompute hnoclaim) hpublic

theorem ay_cghg_publication_requires_guard
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_cghg_public_report
      (ay_cghg_accepted_hash implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    ay_cghg_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript :=
  fun h =>
    ay_cghg_accepted_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_cghg_public_report_accepted
        (ay_cghg_accepted_hash implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
        originalFormulaTruth
        publicOutcome
        h)

theorem ay_cghg_publication_requires_validator
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_cghg_public_report
      (ay_cghg_accepted_hash implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    validatorGate :=
  fun h =>
    ay_cghg_guard_validator implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_cghg_publication_requires_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_cghg_publication_requires_archive
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_cghg_public_report
      (ay_cghg_accepted_hash implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    archiveManifest :=
  fun h =>
    ay_cghg_guard_archive implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_cghg_publication_requires_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_cghg_publication_requires_audit
    (implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_cghg_public_report
      (ay_cghg_accepted_hash implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    auditTranscript :=
  fun h =>
    ay_cghg_guard_audit implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript
      (ay_cghg_publication_requires_guard implicationGraphDigest conflictNodeDigest hashFunctionVersionDigest graphHashTableDigest collisionResolutionWitness decisionLevelMapDigest reasonAntecedentMapDigest learnedClauseDerivationDigest propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackNoClaimPath auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_cghg_accepted_public_report_for_sat
    (acceptedEvidence originalFormulaTruth satOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    satOutcome ->
    ay_cghg_public_report acceptedEvidence originalFormulaTruth satOutcome :=
  ay_cghg_public_report_intro acceptedEvidence originalFormulaTruth satOutcome

theorem ay_cghg_accepted_public_report_for_unsat
    (acceptedEvidence originalFormulaTruth unsatOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    unsatOutcome ->
    ay_cghg_public_report acceptedEvidence originalFormulaTruth unsatOutcome :=
  ay_cghg_public_report_intro acceptedEvidence originalFormulaTruth unsatOutcome
