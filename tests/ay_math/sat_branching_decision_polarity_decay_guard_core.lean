def ay_dpdg_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_dpdg_equisat (before after : Prop) : Prop :=
  ay_dpdg_conj (before -> after) (after -> before)

def ay_dpdg_guard
    (variableDomainDigest : Prop)
    (polarityTableBeforeDigest : Prop)
    (polarityTableAfterDigest : Prop)
    (decayScheduleManifest : Prop)
    (ageCounterLedger : Prop)
    (phaseSavingContextDigest : Prop)
    (decisionOrderReplayTranscript : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackBaseline : Prop)
    (auditTranscript : Prop) : Prop :=
  forall result : Prop,
    (variableDomainDigest ->
      polarityTableBeforeDigest ->
      polarityTableAfterDigest ->
      decayScheduleManifest ->
      ageCounterLedger ->
      phaseSavingContextDigest ->
      decisionOrderReplayTranscript ->
      propagationReplayTranscript ->
      solverBuildEvidence ->
      validatorGate ->
      archiveManifest ->
      fallbackBaseline ->
      auditTranscript ->
      result) ->
    result

def ay_dpdg_agreement
    (variableDomainDigest : Prop)
    (polarityTableBeforeDigest : Prop)
    (polarityTableAfterDigest : Prop)
    (decayScheduleManifest : Prop)
    (ageCounterLedger : Prop)
    (phaseSavingContextDigest : Prop)
    (decisionOrderReplayTranscript : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (auditTranscript : Prop) : Prop :=
  ay_dpdg_guard
    variableDomainDigest
    polarityTableBeforeDigest
    polarityTableAfterDigest
    decayScheduleManifest
    ageCounterLedger
    phaseSavingContextDigest
    decisionOrderReplayTranscript
    propagationReplayTranscript
    solverBuildEvidence
    validatorGate
    archiveManifest
    True
    auditTranscript

def ay_dpdg_accepted_decay
    (variableDomainDigest : Prop)
    (polarityTableBeforeDigest : Prop)
    (polarityTableAfterDigest : Prop)
    (decayScheduleManifest : Prop)
    (ageCounterLedger : Prop)
    (phaseSavingContextDigest : Prop)
    (decisionOrderReplayTranscript : Prop)
    (propagationReplayTranscript : Prop)
    (solverBuildEvidence : Prop)
    (validatorGate : Prop)
    (archiveManifest : Prop)
    (fallbackBaseline : Prop)
    (auditTranscript : Prop) : Prop :=
  ay_dpdg_conj
    (ay_dpdg_guard
      variableDomainDigest
      polarityTableBeforeDigest
      polarityTableAfterDigest
      decayScheduleManifest
      ageCounterLedger
      phaseSavingContextDigest
      decisionOrderReplayTranscript
      propagationReplayTranscript
      solverBuildEvidence
      validatorGate
      archiveManifest
      fallbackBaseline
      auditTranscript)
    (ay_dpdg_agreement
      variableDomainDigest
      polarityTableBeforeDigest
      polarityTableAfterDigest
      decayScheduleManifest
      ageCounterLedger
      phaseSavingContextDigest
      decisionOrderReplayTranscript
      propagationReplayTranscript
      solverBuildEvidence
      validatorGate
      archiveManifest
      auditTranscript)

def ay_dpdg_public_report
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) : Prop :=
  ay_dpdg_conj acceptedEvidence (ay_dpdg_conj originalFormulaTruth publicOutcome)

def ay_dpdg_no_claim (diagnostic fallbackOrRecompute : Prop) : Prop :=
  ay_dpdg_conj diagnostic fallbackOrRecompute

theorem ay_dpdg_conj_intro (left right : Prop) :
    left -> right -> ay_dpdg_conj left right :=
  fun hleft hright result k => k hleft hright

theorem ay_dpdg_conj_left (left right : Prop) :
    ay_dpdg_conj left right -> left :=
  fun h => h left (fun hleft _ => hleft)

theorem ay_dpdg_conj_right (left right : Prop) :
    ay_dpdg_conj left right -> right :=
  fun h => h right (fun _ hright => hright)

theorem ay_dpdg_equisat_intro (before after : Prop) :
    (before -> after) -> (after -> before) -> ay_dpdg_equisat before after :=
  ay_dpdg_conj_intro (before -> after) (after -> before)

theorem ay_dpdg_equisat_forward (before after : Prop) :
    ay_dpdg_equisat before after -> before -> after :=
  ay_dpdg_conj_left (before -> after) (after -> before)

theorem ay_dpdg_equisat_backward (before after : Prop) :
    ay_dpdg_equisat before after -> after -> before :=
  ay_dpdg_conj_right (before -> after) (after -> before)

theorem ay_dpdg_guard_intro
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    variableDomainDigest ->
    polarityTableBeforeDigest ->
    polarityTableAfterDigest ->
    decayScheduleManifest ->
    ageCounterLedger ->
    phaseSavingContextDigest ->
    decisionOrderReplayTranscript ->
    propagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    fallbackBaseline ->
    auditTranscript ->
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript :=
  fun hdomain hbefore hafter hschedule hage hphase hdecision hpropagation hbuild hvalidator harchive hfallback haudit result k =>
    k hdomain hbefore hafter hschedule hage hphase hdecision hpropagation hbuild hvalidator harchive hfallback haudit

theorem ay_dpdg_guard_domain
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    variableDomainDigest :=
  fun h => h variableDomainDigest (fun hdomain _ _ _ _ _ _ _ _ _ _ _ _ => hdomain)

theorem ay_dpdg_guard_polarity_before
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    polarityTableBeforeDigest :=
  fun h => h polarityTableBeforeDigest (fun _ hbefore _ _ _ _ _ _ _ _ _ _ _ => hbefore)

theorem ay_dpdg_guard_polarity_after
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    polarityTableAfterDigest :=
  fun h => h polarityTableAfterDigest (fun _ _ hafter _ _ _ _ _ _ _ _ _ _ => hafter)

theorem ay_dpdg_guard_schedule
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    decayScheduleManifest :=
  fun h => h decayScheduleManifest (fun _ _ _ hschedule _ _ _ _ _ _ _ _ _ => hschedule)

theorem ay_dpdg_guard_age
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    ageCounterLedger :=
  fun h => h ageCounterLedger (fun _ _ _ _ hage _ _ _ _ _ _ _ _ => hage)

theorem ay_dpdg_guard_phase
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    phaseSavingContextDigest :=
  fun h => h phaseSavingContextDigest (fun _ _ _ _ _ hphase _ _ _ _ _ _ _ => hphase)

theorem ay_dpdg_guard_decision
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    decisionOrderReplayTranscript :=
  fun h => h decisionOrderReplayTranscript (fun _ _ _ _ _ _ hdecision _ _ _ _ _ _ => hdecision)

theorem ay_dpdg_guard_propagation
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    propagationReplayTranscript :=
  fun h => h propagationReplayTranscript (fun _ _ _ _ _ _ _ hpropagation _ _ _ _ _ => hpropagation)

theorem ay_dpdg_guard_build
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    solverBuildEvidence :=
  fun h => h solverBuildEvidence (fun _ _ _ _ _ _ _ _ hbuild _ _ _ _ => hbuild)

theorem ay_dpdg_guard_validator
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    validatorGate :=
  fun h => h validatorGate (fun _ _ _ _ _ _ _ _ _ hvalidator _ _ _ => hvalidator)

theorem ay_dpdg_guard_archive
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    archiveManifest :=
  fun h => h archiveManifest (fun _ _ _ _ _ _ _ _ _ _ harchive _ _ => harchive)

theorem ay_dpdg_guard_fallback
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    fallbackBaseline :=
  fun h => h fallbackBaseline (fun _ _ _ _ _ _ _ _ _ _ _ hfallback _ => hfallback)

theorem ay_dpdg_guard_audit
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    auditTranscript :=
  fun h => h auditTranscript (fun _ _ _ _ _ _ _ _ _ _ _ _ haudit => haudit)

theorem ay_dpdg_agreement_intro
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript : Prop) :
    variableDomainDigest ->
    polarityTableBeforeDigest ->
    polarityTableAfterDigest ->
    decayScheduleManifest ->
    ageCounterLedger ->
    phaseSavingContextDigest ->
    decisionOrderReplayTranscript ->
    propagationReplayTranscript ->
    solverBuildEvidence ->
    validatorGate ->
    archiveManifest ->
    auditTranscript ->
    ay_dpdg_agreement variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript :=
  fun hdomain hbefore hafter hschedule hage hphase hdecision hpropagation hbuild hvalidator harchive haudit =>
    ay_dpdg_guard_intro variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest True auditTranscript
      hdomain hbefore hafter hschedule hage hphase hdecision hpropagation hbuild hvalidator harchive True.intro haudit

theorem ay_dpdg_accepted_decay_intro
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    ay_dpdg_agreement variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript ->
    ay_dpdg_accepted_decay variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript :=
  ay_dpdg_conj_intro
    (ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
    (ay_dpdg_agreement variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_dpdg_accepted_guard
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_accepted_decay variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript :=
  ay_dpdg_conj_left
    (ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
    (ay_dpdg_agreement variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_dpdg_accepted_agreement
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript : Prop) :
    ay_dpdg_accepted_decay variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript ->
    ay_dpdg_agreement variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript :=
  ay_dpdg_conj_right
    (ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
    (ay_dpdg_agreement variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest auditTranscript)

theorem ay_dpdg_decay_is_heuristic_only
    (acceptedEvidence heuristicBranchingState : Prop) :
    acceptedEvidence ->
    heuristicBranchingState ->
    ay_dpdg_conj acceptedEvidence heuristicBranchingState :=
  ay_dpdg_conj_intro acceptedEvidence heuristicBranchingState

theorem ay_dpdg_decay_cannot_justify_publication
    (decayEvidence fallbackOrRecompute : Prop) :
    decayEvidence ->
    fallbackOrRecompute ->
    ay_dpdg_no_claim decayEvidence fallbackOrRecompute :=
  ay_dpdg_conj_intro decayEvidence fallbackOrRecompute

theorem ay_dpdg_public_report_intro
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    publicOutcome ->
    ay_dpdg_public_report acceptedEvidence originalFormulaTruth publicOutcome :=
  fun haccepted htruth houtcome =>
    ay_dpdg_conj_intro acceptedEvidence (ay_dpdg_conj originalFormulaTruth publicOutcome)
      haccepted
      (ay_dpdg_conj_intro originalFormulaTruth publicOutcome htruth houtcome)

theorem ay_dpdg_public_report_accepted
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_dpdg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    acceptedEvidence :=
  ay_dpdg_conj_left acceptedEvidence (ay_dpdg_conj originalFormulaTruth publicOutcome)

theorem ay_dpdg_public_report_truth
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_dpdg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    originalFormulaTruth :=
  fun h =>
    ay_dpdg_conj_left originalFormulaTruth publicOutcome
      (ay_dpdg_conj_right acceptedEvidence (ay_dpdg_conj originalFormulaTruth publicOutcome) h)

theorem ay_dpdg_public_report_outcome
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_dpdg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    publicOutcome :=
  fun h =>
    ay_dpdg_conj_right originalFormulaTruth publicOutcome
      (ay_dpdg_conj_right acceptedEvidence (ay_dpdg_conj originalFormulaTruth publicOutcome) h)

theorem ay_dpdg_preserves_formula_truth
    (originalFormulaTruth decayedHeuristicTruth : Prop) :
    ay_dpdg_equisat originalFormulaTruth decayedHeuristicTruth ->
    originalFormulaTruth ->
    decayedHeuristicTruth :=
  ay_dpdg_equisat_forward originalFormulaTruth decayedHeuristicTruth

theorem ay_dpdg_reflects_formula_truth
    (originalFormulaTruth decayedHeuristicTruth : Prop) :
    ay_dpdg_equisat originalFormulaTruth decayedHeuristicTruth ->
    decayedHeuristicTruth ->
    originalFormulaTruth :=
  ay_dpdg_equisat_backward originalFormulaTruth decayedHeuristicTruth

theorem ay_dpdg_accepted_preserves_public_soundness
    (acceptedEvidence originalFormulaTruth publicOutcome : Prop) :
    ay_dpdg_public_report acceptedEvidence originalFormulaTruth publicOutcome ->
    ay_dpdg_conj originalFormulaTruth publicOutcome :=
  ay_dpdg_conj_right acceptedEvidence (ay_dpdg_conj originalFormulaTruth publicOutcome)

theorem ay_dpdg_no_claim_intro (diagnostic fallbackOrRecompute : Prop) :
    diagnostic ->
    fallbackOrRecompute ->
    ay_dpdg_no_claim diagnostic fallbackOrRecompute :=
  ay_dpdg_conj_intro diagnostic fallbackOrRecompute

theorem ay_dpdg_no_claim_recompute (diagnostic fallbackOrRecompute : Prop) :
    ay_dpdg_no_claim diagnostic fallbackOrRecompute ->
    fallbackOrRecompute :=
  ay_dpdg_conj_right diagnostic fallbackOrRecompute

theorem ay_dpdg_domain_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dpdg_no_claim mismatch fallbackOrRecompute :=
  ay_dpdg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dpdg_polarity_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dpdg_no_claim mismatch fallbackOrRecompute :=
  ay_dpdg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dpdg_schedule_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dpdg_no_claim mismatch fallbackOrRecompute :=
  ay_dpdg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dpdg_age_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dpdg_no_claim mismatch fallbackOrRecompute :=
  ay_dpdg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dpdg_phase_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dpdg_no_claim mismatch fallbackOrRecompute :=
  ay_dpdg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dpdg_decision_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dpdg_no_claim mismatch fallbackOrRecompute :=
  ay_dpdg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dpdg_replay_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dpdg_no_claim mismatch fallbackOrRecompute :=
  ay_dpdg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dpdg_build_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dpdg_no_claim mismatch fallbackOrRecompute :=
  ay_dpdg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dpdg_validator_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dpdg_no_claim mismatch fallbackOrRecompute :=
  ay_dpdg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dpdg_archive_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dpdg_no_claim mismatch fallbackOrRecompute :=
  ay_dpdg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dpdg_audit_mismatch_no_claim (mismatch fallbackOrRecompute : Prop) :
    mismatch -> fallbackOrRecompute -> ay_dpdg_no_claim mismatch fallbackOrRecompute :=
  ay_dpdg_no_claim_intro mismatch fallbackOrRecompute

theorem ay_dpdg_failed_guard_cannot_bless_publication
    (failedGuard publicSatOrUnsat fallbackOrRecompute : Prop) :
    ay_dpdg_no_claim failedGuard fallbackOrRecompute ->
    (fallbackOrRecompute -> publicSatOrUnsat -> False) ->
    publicSatOrUnsat ->
    False :=
  fun hnoclaim hblocked hpublic =>
    hblocked (ay_dpdg_no_claim_recompute failedGuard fallbackOrRecompute hnoclaim) hpublic

theorem ay_dpdg_publication_requires_guard
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_dpdg_public_report
      (ay_dpdg_accepted_decay variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    ay_dpdg_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript :=
  fun h =>
    ay_dpdg_accepted_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript
      (ay_dpdg_public_report_accepted
        (ay_dpdg_accepted_decay variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
        originalFormulaTruth
        publicOutcome
        h)

theorem ay_dpdg_publication_requires_validator
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_dpdg_public_report
      (ay_dpdg_accepted_decay variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    validatorGate :=
  fun h =>
    ay_dpdg_guard_validator variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript
      (ay_dpdg_publication_requires_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_dpdg_publication_requires_archive
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_dpdg_public_report
      (ay_dpdg_accepted_decay variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    archiveManifest :=
  fun h =>
    ay_dpdg_guard_archive variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript
      (ay_dpdg_publication_requires_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_dpdg_publication_requires_audit
    (variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome : Prop) :
    ay_dpdg_public_report
      (ay_dpdg_accepted_decay variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript)
      originalFormulaTruth
      publicOutcome ->
    auditTranscript :=
  fun h =>
    ay_dpdg_guard_audit variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript
      (ay_dpdg_publication_requires_guard variableDomainDigest polarityTableBeforeDigest polarityTableAfterDigest decayScheduleManifest ageCounterLedger phaseSavingContextDigest decisionOrderReplayTranscript propagationReplayTranscript solverBuildEvidence validatorGate archiveManifest fallbackBaseline auditTranscript originalFormulaTruth publicOutcome h)

theorem ay_dpdg_accepted_public_report_for_sat
    (acceptedEvidence originalFormulaTruth satOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    satOutcome ->
    ay_dpdg_public_report acceptedEvidence originalFormulaTruth satOutcome :=
  ay_dpdg_public_report_intro acceptedEvidence originalFormulaTruth satOutcome

theorem ay_dpdg_accepted_public_report_for_unsat
    (acceptedEvidence originalFormulaTruth unsatOutcome : Prop) :
    acceptedEvidence ->
    originalFormulaTruth ->
    unsatOutcome ->
    ay_dpdg_public_report acceptedEvidence originalFormulaTruth unsatOutcome :=
  ay_dpdg_public_report_intro acceptedEvidence originalFormulaTruth unsatOutcome
