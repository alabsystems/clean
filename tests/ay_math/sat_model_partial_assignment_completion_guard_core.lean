/-!
  SAT-COMP/ay partial-assignment completion guard.

  This self-contained package models the SAT-only obligations for completing a
  sparse or internal assignment into a total assignment over original variables.
-/

def ay_pacg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_pacg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_pacg_equiv (p q : Prop) : Prop :=
  ay_pacg_conj (p -> q) (q -> p)

def ay_pacg_original_formula_fingerprint
    (partialArtifact originalFingerprintOk : Prop) : Prop :=
  partialArtifact -> originalFingerprintOk

def ay_pacg_variable_domain_digest
    (originalFingerprintOk domainOk : Prop) : Prop :=
  originalFingerprintOk -> domainOk

def ay_pacg_partial_assignment_digest
    (domainOk partialAssignmentOk : Prop) : Prop :=
  domainOk -> partialAssignmentOk

def ay_pacg_completion_policy_manifest
    (partialAssignmentOk completionPolicyOk : Prop) : Prop :=
  partialAssignmentOk -> completionPolicyOk

def ay_pacg_default_value_ledger
    (completionPolicyOk defaultLedgerOk : Prop) : Prop :=
  completionPolicyOk -> defaultLedgerOk

def ay_pacg_dependency_extension_witness
    (defaultLedgerOk extensionWitnessOk : Prop) : Prop :=
  defaultLedgerOk -> extensionWitnessOk

def ay_pacg_completed_assignment_digest
    (extensionWitnessOk completedAssignmentOk : Prop) : Prop :=
  extensionWitnessOk -> completedAssignmentOk

def ay_pacg_original_clause_satisfaction_replay
    (completedAssignmentOk originalClausesSatisfied : Prop) : Prop :=
  completedAssignmentOk -> originalClausesSatisfied

def ay_pacg_parser_transcript
    (originalClausesSatisfied parserOk : Prop) : Prop :=
  originalClausesSatisfied -> parserOk

def ay_pacg_solver_build_evidence (parserOk buildOk : Prop) : Prop :=
  parserOk -> buildOk

def ay_pacg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_pacg_fallback_no_claim_path (validatorOk fallbackReady : Prop) : Prop :=
  validatorOk -> fallbackReady

def ay_pacg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_pacg_accepted_completion
    (originalFp domain partial completionPolicy defaultLedger dependencyWitness completed
     originalReplay parser build validator fallback audit : Prop) : Prop :=
  forall r : Prop,
    (originalFp -> domain -> partial -> completionPolicy -> defaultLedger ->
      dependencyWitness -> completed -> originalReplay -> parser -> build -> validator ->
      fallback -> audit -> r) -> r

def ay_pacg_public_sat
    (accepted completedAssignment partialAgreement originalClausesSatisfied validatorOk
     audited : Prop) : Prop :=
  ay_pacg_conj accepted
    (ay_pacg_conj completedAssignment
      (ay_pacg_conj partialAgreement
        (ay_pacg_conj originalClausesSatisfied
          (ay_pacg_conj validatorOk audited))))

def ay_pacg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_pacg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_pacg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_pacg_conj p q :=
  fun r h => h hp hq

theorem ay_pacg_conj_left {p q : Prop} (h : ay_pacg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_pacg_conj_right {p q : Prop} (h : ay_pacg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_pacg_conj_left h)

theorem ay_pacg_disj_left {p q : Prop} (hp : p) : ay_pacg_disj p q :=
  fun r hl _ => hl hp

theorem ay_pacg_disj_right {p q : Prop} (hq : q) : ay_pacg_disj p q :=
  fun r _ hr => hr hq

theorem ay_pacg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_pacg_equiv p q :=
  ay_pacg_conj_intro hpq hqp

theorem ay_pacg_equiv_forward {p q : Prop} (h : ay_pacg_equiv p q) : p -> q :=
  ay_pacg_conj_left h

theorem ay_pacg_equiv_backward {p q : Prop} (h : ay_pacg_equiv p q) : q -> p :=
  ay_pacg_conj_right h

theorem ay_pacg_original_formula_fingerprint_intro
    {partialArtifact originalFingerprintOk : Prop}
    (h : partialArtifact -> originalFingerprintOk) :
    ay_pacg_original_formula_fingerprint partialArtifact originalFingerprintOk :=
  h

theorem ay_pacg_variable_domain_digest_intro
    {originalFingerprintOk domainOk : Prop}
    (h : originalFingerprintOk -> domainOk) :
    ay_pacg_variable_domain_digest originalFingerprintOk domainOk :=
  h

theorem ay_pacg_partial_assignment_digest_intro
    {domainOk partialAssignmentOk : Prop}
    (h : domainOk -> partialAssignmentOk) :
    ay_pacg_partial_assignment_digest domainOk partialAssignmentOk :=
  h

theorem ay_pacg_completion_policy_manifest_intro
    {partialAssignmentOk completionPolicyOk : Prop}
    (h : partialAssignmentOk -> completionPolicyOk) :
    ay_pacg_completion_policy_manifest partialAssignmentOk completionPolicyOk :=
  h

theorem ay_pacg_default_value_ledger_intro
    {completionPolicyOk defaultLedgerOk : Prop}
    (h : completionPolicyOk -> defaultLedgerOk) :
    ay_pacg_default_value_ledger completionPolicyOk defaultLedgerOk :=
  h

theorem ay_pacg_dependency_extension_witness_intro
    {defaultLedgerOk extensionWitnessOk : Prop}
    (h : defaultLedgerOk -> extensionWitnessOk) :
    ay_pacg_dependency_extension_witness defaultLedgerOk extensionWitnessOk :=
  h

theorem ay_pacg_completed_assignment_digest_intro
    {extensionWitnessOk completedAssignmentOk : Prop}
    (h : extensionWitnessOk -> completedAssignmentOk) :
    ay_pacg_completed_assignment_digest extensionWitnessOk completedAssignmentOk :=
  h

theorem ay_pacg_original_clause_satisfaction_replay_intro
    {completedAssignmentOk originalClausesSatisfied : Prop}
    (h : completedAssignmentOk -> originalClausesSatisfied) :
    ay_pacg_original_clause_satisfaction_replay completedAssignmentOk
      originalClausesSatisfied :=
  h

theorem ay_pacg_parser_transcript_intro {originalClausesSatisfied parserOk : Prop}
    (h : originalClausesSatisfied -> parserOk) :
    ay_pacg_parser_transcript originalClausesSatisfied parserOk :=
  h

theorem ay_pacg_solver_build_evidence_intro {parserOk buildOk : Prop}
    (h : parserOk -> buildOk) :
    ay_pacg_solver_build_evidence parserOk buildOk :=
  h

theorem ay_pacg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_pacg_validator_gate buildOk validatorOk :=
  h

theorem ay_pacg_fallback_no_claim_path_intro {validatorOk fallbackReady : Prop}
    (h : validatorOk -> fallbackReady) :
    ay_pacg_fallback_no_claim_path validatorOk fallbackReady :=
  h

theorem ay_pacg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_pacg_audit_transcript fallbackReady audited :=
  h

theorem ay_pacg_accepted_completion_intro
    {originalFp domain partial completionPolicy defaultLedger dependencyWitness completed
     originalReplay parser build validator fallback audit : Prop}
    (hof : originalFp) (hd : domain) (hp : partial) (hcp : completionPolicy)
    (hdl : defaultLedger) (hdw : dependencyWitness) (hc : completed)
    (hor : originalReplay) (hpt : parser) (hb : build) (hv : validator)
    (hfb : fallback) (hau : audit) :
    ay_pacg_accepted_completion originalFp domain partial completionPolicy defaultLedger
      dependencyWitness completed originalReplay parser build validator fallback audit :=
  fun r k => k hof hd hp hcp hdl hdw hc hor hpt hb hv hfb hau

theorem ay_pacg_accepted_completion_domain
    {originalFp domain partial completionPolicy defaultLedger dependencyWitness completed
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_pacg_accepted_completion originalFp domain partial completionPolicy defaultLedger
      dependencyWitness completed originalReplay parser build validator fallback audit) :
    domain :=
  h domain (fun _ hd _ _ _ _ _ _ _ _ _ _ _ => hd)

theorem ay_pacg_accepted_completion_partial
    {originalFp domain partial completionPolicy defaultLedger dependencyWitness completed
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_pacg_accepted_completion originalFp domain partial completionPolicy defaultLedger
      dependencyWitness completed originalReplay parser build validator fallback audit) :
    partial :=
  h partial (fun _ _ hp _ _ _ _ _ _ _ _ _ _ => hp)

theorem ay_pacg_accepted_completion_policy
    {originalFp domain partial completionPolicy defaultLedger dependencyWitness completed
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_pacg_accepted_completion originalFp domain partial completionPolicy defaultLedger
      dependencyWitness completed originalReplay parser build validator fallback audit) :
    completionPolicy :=
  h completionPolicy (fun _ _ _ hcp _ _ _ _ _ _ _ _ _ => hcp)

theorem ay_pacg_accepted_completion_default_ledger
    {originalFp domain partial completionPolicy defaultLedger dependencyWitness completed
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_pacg_accepted_completion originalFp domain partial completionPolicy defaultLedger
      dependencyWitness completed originalReplay parser build validator fallback audit) :
    defaultLedger :=
  h defaultLedger (fun _ _ _ _ hdl _ _ _ _ _ _ _ _ => hdl)

theorem ay_pacg_accepted_completion_dependency_witness
    {originalFp domain partial completionPolicy defaultLedger dependencyWitness completed
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_pacg_accepted_completion originalFp domain partial completionPolicy defaultLedger
      dependencyWitness completed originalReplay parser build validator fallback audit) :
    dependencyWitness :=
  h dependencyWitness (fun _ _ _ _ _ hdw _ _ _ _ _ _ _ => hdw)

theorem ay_pacg_accepted_completion_completed
    {originalFp domain partial completionPolicy defaultLedger dependencyWitness completed
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_pacg_accepted_completion originalFp domain partial completionPolicy defaultLedger
      dependencyWitness completed originalReplay parser build validator fallback audit) :
    completed :=
  h completed (fun _ _ _ _ _ _ hc _ _ _ _ _ _ => hc)

theorem ay_pacg_accepted_completion_original_replay
    {originalFp domain partial completionPolicy defaultLedger dependencyWitness completed
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_pacg_accepted_completion originalFp domain partial completionPolicy defaultLedger
      dependencyWitness completed originalReplay parser build validator fallback audit) :
    originalReplay :=
  h originalReplay (fun _ _ _ _ _ _ _ hor _ _ _ _ _ => hor)

theorem ay_pacg_accepted_completion_validator
    {originalFp domain partial completionPolicy defaultLedger dependencyWitness completed
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_pacg_accepted_completion originalFp domain partial completionPolicy defaultLedger
      dependencyWitness completed originalReplay parser build validator fallback audit) :
    validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ _ hv _ _ => hv)

theorem ay_pacg_accepted_completion_audit
    {originalFp domain partial completionPolicy defaultLedger dependencyWitness completed
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_pacg_accepted_completion originalFp domain partial completionPolicy defaultLedger
      dependencyWitness completed originalReplay parser build validator fallback audit) :
    audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_pacg_public_sat_intro
    {accepted completedAssignment partialAgreement originalClausesSatisfied validatorOk
     audited : Prop}
    (ha : accepted) (hc : completedAssignment) (hp : partialAgreement)
    (hor : originalClausesSatisfied) (hv : validatorOk) (hau : audited) :
    ay_pacg_public_sat accepted completedAssignment partialAgreement
      originalClausesSatisfied validatorOk audited :=
  ay_pacg_conj_intro ha
    (ay_pacg_conj_intro hc
      (ay_pacg_conj_intro hp
        (ay_pacg_conj_intro hor (ay_pacg_conj_intro hv hau))))

theorem ay_pacg_public_sat_requires_completion_guard
    {accepted completedAssignment partialAgreement originalClausesSatisfied validatorOk
     audited : Prop}
    (h : ay_pacg_public_sat accepted completedAssignment partialAgreement
      originalClausesSatisfied validatorOk audited) : accepted :=
  ay_pacg_conj_left h

theorem ay_pacg_public_sat_completed_assignment
    {accepted completedAssignment partialAgreement originalClausesSatisfied validatorOk
     audited : Prop}
    (h : ay_pacg_public_sat accepted completedAssignment partialAgreement
      originalClausesSatisfied validatorOk audited) : completedAssignment :=
  ay_pacg_conj_left (ay_pacg_conj_right h)

theorem ay_pacg_public_sat_partial_agreement
    {accepted completedAssignment partialAgreement originalClausesSatisfied validatorOk
     audited : Prop}
    (h : ay_pacg_public_sat accepted completedAssignment partialAgreement
      originalClausesSatisfied validatorOk audited) : partialAgreement :=
  ay_pacg_conj_left (ay_pacg_conj_right (ay_pacg_conj_right h))

theorem ay_pacg_public_sat_original_clauses
    {accepted completedAssignment partialAgreement originalClausesSatisfied validatorOk
     audited : Prop}
    (h : ay_pacg_public_sat accepted completedAssignment partialAgreement
      originalClausesSatisfied validatorOk audited) : originalClausesSatisfied :=
  ay_pacg_conj_left
    (ay_pacg_conj_right (ay_pacg_conj_right (ay_pacg_conj_right h)))

theorem ay_pacg_accepted_completion_turns_partial_into_original_sat
    {originalFp domain partial completionPolicy defaultLedger dependencyWitness completed
     originalReplay parser build validator fallback audit : Prop}
    (h : ay_pacg_accepted_completion originalFp domain partial completionPolicy
      defaultLedger dependencyWitness completed originalReplay parser build validator fallback
      audit) :
    ay_pacg_public_sat
      (ay_pacg_accepted_completion originalFp domain partial completionPolicy defaultLedger
        dependencyWitness completed originalReplay parser build validator fallback audit)
      completed partial originalReplay validator audit :=
  ay_pacg_public_sat_intro
    h
    (ay_pacg_accepted_completion_completed h)
    (ay_pacg_accepted_completion_partial h)
    (ay_pacg_accepted_completion_original_replay h)
    (ay_pacg_accepted_completion_validator h)
    (ay_pacg_accepted_completion_audit h)

theorem ay_pacg_completed_assignment_agrees_with_partial
    {partialAssignment completedAssignment assignedVariablesAgree : Prop}
    (h : ay_pacg_equiv partialAssignment completedAssignment)
    (hp : completedAssignment -> assignedVariablesAgree)
    (hpartial : partialAssignment) : assignedVariablesAgree :=
  hp (ay_pacg_equiv_forward h hpartial)

theorem ay_pacg_no_claim_intro {reason : Prop} (h : reason) :
    ay_pacg_no_claim_diagnostic reason :=
  h

theorem ay_pacg_recompute_intro {reason : Prop} (h : reason) :
    ay_pacg_recompute_obligation reason :=
  h

theorem ay_pacg_domain_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_pacg_no_claim_diagnostic mismatch :=
  ay_pacg_no_claim_intro h

theorem ay_pacg_partial_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_pacg_recompute_obligation mismatch :=
  ay_pacg_recompute_intro h

theorem ay_pacg_completion_policy_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_pacg_no_claim_diagnostic mismatch :=
  ay_pacg_no_claim_intro h

theorem ay_pacg_default_ledger_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_pacg_recompute_obligation mismatch :=
  ay_pacg_recompute_intro h

theorem ay_pacg_dependency_witness_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_pacg_recompute_obligation mismatch :=
  ay_pacg_recompute_intro h

theorem ay_pacg_replay_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_pacg_no_claim_diagnostic mismatch :=
  ay_pacg_no_claim_intro h

theorem ay_pacg_parser_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_pacg_recompute_obligation mismatch :=
  ay_pacg_recompute_intro h

theorem ay_pacg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_pacg_recompute_obligation mismatch :=
  ay_pacg_recompute_intro h

theorem ay_pacg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_pacg_no_claim_diagnostic mismatch :=
  ay_pacg_no_claim_intro h

theorem ay_pacg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_pacg_no_claim_diagnostic mismatch :=
  ay_pacg_no_claim_intro h

theorem ay_pacg_failed_completion_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_pacg_no_claim_diagnostic failure)
    (noBless : ay_pacg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_pacg_failed_completion_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_pacg_recompute_obligation failure)
    (hfailure : failure) :
    ay_pacg_recompute_obligation failure :=
  fallback hfailure
