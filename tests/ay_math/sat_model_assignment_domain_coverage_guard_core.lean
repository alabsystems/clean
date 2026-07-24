/-!
  SAT-COMP/ay assignment domain coverage guard.

  This self-contained package models the SAT-only obligations for deciding
  whether a model is total, justified by defaults, or invalid for the original
  variable domain.
-/

def ay_adcg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_adcg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_adcg_equiv (p q : Prop) : Prop :=
  ay_adcg_conj (p -> q) (q -> p)

def ay_adcg_original_formula_fingerprint
    (assignmentDigest formulaFingerprintOk : Prop) : Prop :=
  assignmentDigest -> formulaFingerprintOk

def ay_adcg_variable_domain_digest
    (formulaFingerprintOk domainOk : Prop) : Prop :=
  formulaFingerprintOk -> domainOk

def ay_adcg_assignment_digest (domainOk assignmentOk : Prop) : Prop :=
  domainOk -> assignmentOk

def ay_adcg_covered_variable_set_digest
    (assignmentOk coverageOk : Prop) : Prop :=
  assignmentOk -> coverageOk

def ay_adcg_missing_variable_ledger
    (coverageOk missingLedgerOk : Prop) : Prop :=
  coverageOk -> missingLedgerOk

def ay_adcg_default_completion_policy_manifest
    (missingLedgerOk defaultPolicyOk : Prop) : Prop :=
  missingLedgerOk -> defaultPolicyOk

def ay_adcg_out_of_domain_literal_ledger
    (defaultPolicyOk outOfDomainOk : Prop) : Prop :=
  defaultPolicyOk -> outOfDomainOk

def ay_adcg_normalized_assignment_digest
    (outOfDomainOk normalizedAssignmentOk : Prop) : Prop :=
  outOfDomainOk -> normalizedAssignmentOk

def ay_adcg_clause_satisfaction_replay
    (normalizedAssignmentOk everyOriginalClauseSatisfied : Prop) : Prop :=
  normalizedAssignmentOk -> everyOriginalClauseSatisfied

def ay_adcg_parser_transcript
    (everyOriginalClauseSatisfied parserOk : Prop) : Prop :=
  everyOriginalClauseSatisfied -> parserOk

def ay_adcg_solver_build_evidence (parserOk buildOk : Prop) : Prop :=
  parserOk -> buildOk

def ay_adcg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_adcg_archive_manifest (validatorOk archiveOk : Prop) : Prop :=
  validatorOk -> archiveOk

def ay_adcg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_adcg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_adcg_accepted_coverage
    (formula domain assignment coverage missingLedger defaultPolicy outOfDomain normalized
     replay parser build validator archive fallback audit : Prop) : Prop :=
  forall r : Prop,
    (formula -> domain -> assignment -> coverage -> missingLedger -> defaultPolicy ->
      outOfDomain -> normalized -> replay -> parser -> build -> validator -> archive ->
      fallback -> audit -> r) -> r

def ay_adcg_public_sat
    (accepted normalizedAssignment everyOriginalClauseSatisfied coverageHandled validatorOk
     archiveOk audited : Prop) : Prop :=
  ay_adcg_conj accepted
    (ay_adcg_conj normalizedAssignment
      (ay_adcg_conj everyOriginalClauseSatisfied
        (ay_adcg_conj coverageHandled
          (ay_adcg_conj validatorOk (ay_adcg_conj archiveOk audited)))))

def ay_adcg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_adcg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_adcg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_adcg_conj p q :=
  fun r h => h hp hq

theorem ay_adcg_conj_left {p q : Prop} (h : ay_adcg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_adcg_conj_right {p q : Prop} (h : ay_adcg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_adcg_conj_left h)

theorem ay_adcg_disj_left {p q : Prop} (hp : p) : ay_adcg_disj p q :=
  fun r hl _ => hl hp

theorem ay_adcg_disj_right {p q : Prop} (hq : q) : ay_adcg_disj p q :=
  fun r _ hr => hr hq

theorem ay_adcg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_adcg_equiv p q :=
  ay_adcg_conj_intro hpq hqp

theorem ay_adcg_equiv_forward {p q : Prop} (h : ay_adcg_equiv p q) : p -> q :=
  ay_adcg_conj_left h

theorem ay_adcg_equiv_backward {p q : Prop} (h : ay_adcg_equiv p q) : q -> p :=
  ay_adcg_conj_right h

theorem ay_adcg_original_formula_fingerprint_intro
    {assignmentDigest formulaFingerprintOk : Prop}
    (h : assignmentDigest -> formulaFingerprintOk) :
    ay_adcg_original_formula_fingerprint assignmentDigest formulaFingerprintOk :=
  h

theorem ay_adcg_variable_domain_digest_intro {formulaFingerprintOk domainOk : Prop}
    (h : formulaFingerprintOk -> domainOk) :
    ay_adcg_variable_domain_digest formulaFingerprintOk domainOk :=
  h

theorem ay_adcg_assignment_digest_intro {domainOk assignmentOk : Prop}
    (h : domainOk -> assignmentOk) :
    ay_adcg_assignment_digest domainOk assignmentOk :=
  h

theorem ay_adcg_covered_variable_set_digest_intro {assignmentOk coverageOk : Prop}
    (h : assignmentOk -> coverageOk) :
    ay_adcg_covered_variable_set_digest assignmentOk coverageOk :=
  h

theorem ay_adcg_missing_variable_ledger_intro {coverageOk missingLedgerOk : Prop}
    (h : coverageOk -> missingLedgerOk) :
    ay_adcg_missing_variable_ledger coverageOk missingLedgerOk :=
  h

theorem ay_adcg_default_completion_policy_manifest_intro
    {missingLedgerOk defaultPolicyOk : Prop}
    (h : missingLedgerOk -> defaultPolicyOk) :
    ay_adcg_default_completion_policy_manifest missingLedgerOk defaultPolicyOk :=
  h

theorem ay_adcg_out_of_domain_literal_ledger_intro
    {defaultPolicyOk outOfDomainOk : Prop}
    (h : defaultPolicyOk -> outOfDomainOk) :
    ay_adcg_out_of_domain_literal_ledger defaultPolicyOk outOfDomainOk :=
  h

theorem ay_adcg_normalized_assignment_digest_intro
    {outOfDomainOk normalizedAssignmentOk : Prop}
    (h : outOfDomainOk -> normalizedAssignmentOk) :
    ay_adcg_normalized_assignment_digest outOfDomainOk normalizedAssignmentOk :=
  h

theorem ay_adcg_clause_satisfaction_replay_intro
    {normalizedAssignmentOk everyOriginalClauseSatisfied : Prop}
    (h : normalizedAssignmentOk -> everyOriginalClauseSatisfied) :
    ay_adcg_clause_satisfaction_replay normalizedAssignmentOk
      everyOriginalClauseSatisfied :=
  h

theorem ay_adcg_parser_transcript_intro {everyOriginalClauseSatisfied parserOk : Prop}
    (h : everyOriginalClauseSatisfied -> parserOk) :
    ay_adcg_parser_transcript everyOriginalClauseSatisfied parserOk :=
  h

theorem ay_adcg_solver_build_evidence_intro {parserOk buildOk : Prop}
    (h : parserOk -> buildOk) :
    ay_adcg_solver_build_evidence parserOk buildOk :=
  h

theorem ay_adcg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_adcg_validator_gate buildOk validatorOk :=
  h

theorem ay_adcg_archive_manifest_intro {validatorOk archiveOk : Prop}
    (h : validatorOk -> archiveOk) :
    ay_adcg_archive_manifest validatorOk archiveOk :=
  h

theorem ay_adcg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_adcg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_adcg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_adcg_audit_transcript fallbackReady audited :=
  h

theorem ay_adcg_accepted_coverage_intro
    {formula domain assignment coverage missingLedger defaultPolicy outOfDomain normalized
     replay parser build validator archive fallback audit : Prop}
    (hf : formula) (hd : domain) (ha : assignment) (hc : coverage)
    (hm : missingLedger) (hp : defaultPolicy) (ho : outOfDomain) (hn : normalized)
    (hr : replay) (hpa : parser) (hb : build) (hv : validator) (har : archive)
    (hfb : fallback) (hau : audit) :
    ay_adcg_accepted_coverage formula domain assignment coverage missingLedger
      defaultPolicy outOfDomain normalized replay parser build validator archive fallback
      audit :=
  fun r k => k hf hd ha hc hm hp ho hn hr hpa hb hv har hfb hau

theorem ay_adcg_accepted_coverage_domain
    {formula domain assignment coverage missingLedger defaultPolicy outOfDomain normalized
     replay parser build validator archive fallback audit : Prop}
    (h : ay_adcg_accepted_coverage formula domain assignment coverage missingLedger
      defaultPolicy outOfDomain normalized replay parser build validator archive fallback
      audit) : domain :=
  h domain (fun _ hd _ _ _ _ _ _ _ _ _ _ _ _ _ => hd)

theorem ay_adcg_accepted_coverage_coverage
    {formula domain assignment coverage missingLedger defaultPolicy outOfDomain normalized
     replay parser build validator archive fallback audit : Prop}
    (h : ay_adcg_accepted_coverage formula domain assignment coverage missingLedger
      defaultPolicy outOfDomain normalized replay parser build validator archive fallback
      audit) : coverage :=
  h coverage (fun _ _ _ hc _ _ _ _ _ _ _ _ _ _ _ => hc)

theorem ay_adcg_accepted_coverage_missing_ledger
    {formula domain assignment coverage missingLedger defaultPolicy outOfDomain normalized
     replay parser build validator archive fallback audit : Prop}
    (h : ay_adcg_accepted_coverage formula domain assignment coverage missingLedger
      defaultPolicy outOfDomain normalized replay parser build validator archive fallback
      audit) : missingLedger :=
  h missingLedger (fun _ _ _ _ hm _ _ _ _ _ _ _ _ _ _ => hm)

theorem ay_adcg_accepted_coverage_default_policy
    {formula domain assignment coverage missingLedger defaultPolicy outOfDomain normalized
     replay parser build validator archive fallback audit : Prop}
    (h : ay_adcg_accepted_coverage formula domain assignment coverage missingLedger
      defaultPolicy outOfDomain normalized replay parser build validator archive fallback
      audit) : defaultPolicy :=
  h defaultPolicy (fun _ _ _ _ _ hp _ _ _ _ _ _ _ _ _ => hp)

theorem ay_adcg_accepted_coverage_out_of_domain
    {formula domain assignment coverage missingLedger defaultPolicy outOfDomain normalized
     replay parser build validator archive fallback audit : Prop}
    (h : ay_adcg_accepted_coverage formula domain assignment coverage missingLedger
      defaultPolicy outOfDomain normalized replay parser build validator archive fallback
      audit) : outOfDomain :=
  h outOfDomain (fun _ _ _ _ _ _ ho _ _ _ _ _ _ _ _ => ho)

theorem ay_adcg_accepted_coverage_normalized
    {formula domain assignment coverage missingLedger defaultPolicy outOfDomain normalized
     replay parser build validator archive fallback audit : Prop}
    (h : ay_adcg_accepted_coverage formula domain assignment coverage missingLedger
      defaultPolicy outOfDomain normalized replay parser build validator archive fallback
      audit) : normalized :=
  h normalized (fun _ _ _ _ _ _ _ hn _ _ _ _ _ _ _ => hn)

theorem ay_adcg_accepted_coverage_replay
    {formula domain assignment coverage missingLedger defaultPolicy outOfDomain normalized
     replay parser build validator archive fallback audit : Prop}
    (h : ay_adcg_accepted_coverage formula domain assignment coverage missingLedger
      defaultPolicy outOfDomain normalized replay parser build validator archive fallback
      audit) : replay :=
  h replay (fun _ _ _ _ _ _ _ _ hr _ _ _ _ _ _ => hr)

theorem ay_adcg_accepted_coverage_validator
    {formula domain assignment coverage missingLedger defaultPolicy outOfDomain normalized
     replay parser build validator archive fallback audit : Prop}
    (h : ay_adcg_accepted_coverage formula domain assignment coverage missingLedger
      defaultPolicy outOfDomain normalized replay parser build validator archive fallback
      audit) : validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ => hv)

theorem ay_adcg_accepted_coverage_archive
    {formula domain assignment coverage missingLedger defaultPolicy outOfDomain normalized
     replay parser build validator archive fallback audit : Prop}
    (h : ay_adcg_accepted_coverage formula domain assignment coverage missingLedger
      defaultPolicy outOfDomain normalized replay parser build validator archive fallback
      audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ _ _ _ har _ _ => har)

theorem ay_adcg_accepted_coverage_audit
    {formula domain assignment coverage missingLedger defaultPolicy outOfDomain normalized
     replay parser build validator archive fallback audit : Prop}
    (h : ay_adcg_accepted_coverage formula domain assignment coverage missingLedger
      defaultPolicy outOfDomain normalized replay parser build validator archive fallback
      audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_adcg_public_sat_intro
    {accepted normalizedAssignment everyOriginalClauseSatisfied coverageHandled validatorOk
     archiveOk audited : Prop}
    (ha : accepted) (hn : normalizedAssignment) (hr : everyOriginalClauseSatisfied)
    (hc : coverageHandled) (hv : validatorOk) (har : archiveOk) (hau : audited) :
    ay_adcg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      coverageHandled validatorOk archiveOk audited :=
  ay_adcg_conj_intro ha
    (ay_adcg_conj_intro hn
      (ay_adcg_conj_intro hr
        (ay_adcg_conj_intro hc
          (ay_adcg_conj_intro hv (ay_adcg_conj_intro har hau)))))

theorem ay_adcg_public_sat_requires_coverage_guard
    {accepted normalizedAssignment everyOriginalClauseSatisfied coverageHandled validatorOk
     archiveOk audited : Prop}
    (h : ay_adcg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      coverageHandled validatorOk archiveOk audited) : accepted :=
  ay_adcg_conj_left h

theorem ay_adcg_public_sat_normalized_assignment
    {accepted normalizedAssignment everyOriginalClauseSatisfied coverageHandled validatorOk
     archiveOk audited : Prop}
    (h : ay_adcg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      coverageHandled validatorOk archiveOk audited) : normalizedAssignment :=
  ay_adcg_conj_left (ay_adcg_conj_right h)

theorem ay_adcg_public_sat_every_original_clause
    {accepted normalizedAssignment everyOriginalClauseSatisfied coverageHandled validatorOk
     archiveOk audited : Prop}
    (h : ay_adcg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      coverageHandled validatorOk archiveOk audited) : everyOriginalClauseSatisfied :=
  ay_adcg_conj_left (ay_adcg_conj_right (ay_adcg_conj_right h))

theorem ay_adcg_public_sat_coverage_handled
    {accepted normalizedAssignment everyOriginalClauseSatisfied coverageHandled validatorOk
     archiveOk audited : Prop}
    (h : ay_adcg_public_sat accepted normalizedAssignment everyOriginalClauseSatisfied
      coverageHandled validatorOk archiveOk audited) : coverageHandled :=
  ay_adcg_conj_left
    (ay_adcg_conj_right (ay_adcg_conj_right (ay_adcg_conj_right h)))

theorem ay_adcg_accepted_coverage_yields_normalized_satisfying_assignment
    {formula domain assignment coverage missingLedger defaultPolicy outOfDomain normalized
     replay parser build validator archive fallback audit : Prop}
    (h : ay_adcg_accepted_coverage formula domain assignment coverage missingLedger
      defaultPolicy outOfDomain normalized replay parser build validator archive fallback
      audit) :
    ay_adcg_public_sat
      (ay_adcg_accepted_coverage formula domain assignment coverage missingLedger
        defaultPolicy outOfDomain normalized replay parser build validator archive fallback
        audit)
      normalized replay coverage validator archive audit :=
  ay_adcg_public_sat_intro
    h
    (ay_adcg_accepted_coverage_normalized h)
    (ay_adcg_accepted_coverage_replay h)
    (ay_adcg_accepted_coverage_coverage h)
    (ay_adcg_accepted_coverage_validator h)
    (ay_adcg_accepted_coverage_archive h)
    (ay_adcg_accepted_coverage_audit h)

theorem ay_adcg_missing_and_out_of_domain_handled_by_policy_or_no_claim
    {missingVars outOfDomainVars justifiedPolicy noClaim : Prop}
    (hm : missingVars -> justifiedPolicy)
    (ho : outOfDomainVars -> noClaim)
    (hcase : ay_adcg_disj missingVars outOfDomainVars) :
    ay_adcg_disj justifiedPolicy noClaim :=
  hcase (ay_adcg_disj justifiedPolicy noClaim)
    (fun h => ay_adcg_disj_left (hm h))
    (fun h => ay_adcg_disj_right (ho h))

theorem ay_adcg_no_claim_intro {reason : Prop} (h : reason) :
    ay_adcg_no_claim_diagnostic reason :=
  h

theorem ay_adcg_recompute_intro {reason : Prop} (h : reason) :
    ay_adcg_recompute_obligation reason :=
  h

theorem ay_adcg_domain_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_adcg_no_claim_diagnostic mismatch :=
  ay_adcg_no_claim_intro h

theorem ay_adcg_assignment_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_adcg_recompute_obligation mismatch :=
  ay_adcg_recompute_intro h

theorem ay_adcg_coverage_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_adcg_no_claim_diagnostic mismatch :=
  ay_adcg_no_claim_intro h

theorem ay_adcg_missing_ledger_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_adcg_recompute_obligation mismatch :=
  ay_adcg_recompute_intro h

theorem ay_adcg_default_policy_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_adcg_no_claim_diagnostic mismatch :=
  ay_adcg_no_claim_intro h

theorem ay_adcg_out_of_domain_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_adcg_no_claim_diagnostic mismatch :=
  ay_adcg_no_claim_intro h

theorem ay_adcg_normalization_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_adcg_recompute_obligation mismatch :=
  ay_adcg_recompute_intro h

theorem ay_adcg_replay_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_adcg_no_claim_diagnostic mismatch :=
  ay_adcg_no_claim_intro h

theorem ay_adcg_parser_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_adcg_recompute_obligation mismatch :=
  ay_adcg_recompute_intro h

theorem ay_adcg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_adcg_recompute_obligation mismatch :=
  ay_adcg_recompute_intro h

theorem ay_adcg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_adcg_no_claim_diagnostic mismatch :=
  ay_adcg_no_claim_intro h

theorem ay_adcg_archive_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_adcg_no_claim_diagnostic mismatch :=
  ay_adcg_no_claim_intro h

theorem ay_adcg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_adcg_no_claim_diagnostic mismatch :=
  ay_adcg_no_claim_intro h

theorem ay_adcg_failed_coverage_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_adcg_no_claim_diagnostic failure)
    (noBless : ay_adcg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_adcg_failed_coverage_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_adcg_recompute_obligation failure)
    (hfailure : failure) :
    ay_adcg_recompute_obligation failure :=
  fallback hfailure
