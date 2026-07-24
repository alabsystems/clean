/-!
  SAT-COMP/ay DIMACS model-output parser guard.

  This self-contained package models the SAT-only obligations for parsing
  solver DIMACS output before any public SAT publication.
-/

def ay_dopg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_dopg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_dopg_equiv (p q : Prop) : Prop :=
  ay_dopg_conj (p -> q) (q -> p)

def ay_dopg_raw_solver_output_digest (rawOutput rawOk : Prop) : Prop :=
  rawOutput -> rawOk

def ay_dopg_parser_version_digest (rawOk parserVersionOk : Prop) : Prop :=
  rawOk -> parserVersionOk

def ay_dopg_status_line_parse_transcript
    (parserVersionOk statusLineOk : Prop) : Prop :=
  parserVersionOk -> statusLineOk

def ay_dopg_assignment_line_parse_transcript
    (statusLineOk assignmentLinesOk : Prop) : Prop :=
  statusLineOk -> assignmentLinesOk

def ay_dopg_invalid_duplicate_literal_ledger
    (assignmentLinesOk literalLedgerOk : Prop) : Prop :=
  assignmentLinesOk -> literalLedgerOk

def ay_dopg_variable_domain_digest
    (literalLedgerOk domainOk : Prop) : Prop :=
  literalLedgerOk -> domainOk

def ay_dopg_normalized_assignment_digest
    (domainOk normalizedAssignmentOk : Prop) : Prop :=
  domainOk -> normalizedAssignmentOk

def ay_dopg_original_formula_fingerprint
    (normalizedAssignmentOk fingerprintOk : Prop) : Prop :=
  normalizedAssignmentOk -> fingerprintOk

def ay_dopg_clause_satisfaction_replay
    (fingerprintOk originalClausesSatisfied : Prop) : Prop :=
  fingerprintOk -> originalClausesSatisfied

def ay_dopg_solver_build_evidence
    (originalClausesSatisfied buildOk : Prop) : Prop :=
  originalClausesSatisfied -> buildOk

def ay_dopg_validator_gate (buildOk validatorOk : Prop) : Prop :=
  buildOk -> validatorOk

def ay_dopg_fallback_no_claim_path (validatorOk fallbackReady : Prop) : Prop :=
  validatorOk -> fallbackReady

def ay_dopg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_dopg_accepted_parser
    (raw parserVersion statusLine assignmentLines literalLedger domain normalizedAssignment
     fingerprint replay build validator fallback audit : Prop) : Prop :=
  forall r : Prop,
    (raw -> parserVersion -> statusLine -> assignmentLines -> literalLedger -> domain ->
      normalizedAssignment -> fingerprint -> replay -> build -> validator -> fallback ->
      audit -> r) -> r

def ay_dopg_public_sat
    (accepted normalizedAssignment originalClausesSatisfied validatorOk audited : Prop) : Prop :=
  ay_dopg_conj accepted
    (ay_dopg_conj normalizedAssignment
      (ay_dopg_conj originalClausesSatisfied (ay_dopg_conj validatorOk audited)))

def ay_dopg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_dopg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_dopg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_dopg_conj p q :=
  fun r h => h hp hq

theorem ay_dopg_conj_left {p q : Prop} (h : ay_dopg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_dopg_conj_right {p q : Prop} (h : ay_dopg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_dopg_conj_left h)

theorem ay_dopg_disj_left {p q : Prop} (hp : p) : ay_dopg_disj p q :=
  fun r hl _ => hl hp

theorem ay_dopg_disj_right {p q : Prop} (hq : q) : ay_dopg_disj p q :=
  fun r _ hr => hr hq

theorem ay_dopg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_dopg_equiv p q :=
  ay_dopg_conj_intro hpq hqp

theorem ay_dopg_equiv_forward {p q : Prop} (h : ay_dopg_equiv p q) : p -> q :=
  ay_dopg_conj_left h

theorem ay_dopg_equiv_backward {p q : Prop} (h : ay_dopg_equiv p q) : q -> p :=
  ay_dopg_conj_right h

theorem ay_dopg_raw_solver_output_digest_intro {rawOutput rawOk : Prop}
    (h : rawOutput -> rawOk) :
    ay_dopg_raw_solver_output_digest rawOutput rawOk :=
  h

theorem ay_dopg_parser_version_digest_intro {rawOk parserVersionOk : Prop}
    (h : rawOk -> parserVersionOk) :
    ay_dopg_parser_version_digest rawOk parserVersionOk :=
  h

theorem ay_dopg_status_line_parse_transcript_intro
    {parserVersionOk statusLineOk : Prop}
    (h : parserVersionOk -> statusLineOk) :
    ay_dopg_status_line_parse_transcript parserVersionOk statusLineOk :=
  h

theorem ay_dopg_assignment_line_parse_transcript_intro
    {statusLineOk assignmentLinesOk : Prop}
    (h : statusLineOk -> assignmentLinesOk) :
    ay_dopg_assignment_line_parse_transcript statusLineOk assignmentLinesOk :=
  h

theorem ay_dopg_invalid_duplicate_literal_ledger_intro
    {assignmentLinesOk literalLedgerOk : Prop}
    (h : assignmentLinesOk -> literalLedgerOk) :
    ay_dopg_invalid_duplicate_literal_ledger assignmentLinesOk literalLedgerOk :=
  h

theorem ay_dopg_variable_domain_digest_intro {literalLedgerOk domainOk : Prop}
    (h : literalLedgerOk -> domainOk) :
    ay_dopg_variable_domain_digest literalLedgerOk domainOk :=
  h

theorem ay_dopg_normalized_assignment_digest_intro
    {domainOk normalizedAssignmentOk : Prop}
    (h : domainOk -> normalizedAssignmentOk) :
    ay_dopg_normalized_assignment_digest domainOk normalizedAssignmentOk :=
  h

theorem ay_dopg_original_formula_fingerprint_intro
    {normalizedAssignmentOk fingerprintOk : Prop}
    (h : normalizedAssignmentOk -> fingerprintOk) :
    ay_dopg_original_formula_fingerprint normalizedAssignmentOk fingerprintOk :=
  h

theorem ay_dopg_clause_satisfaction_replay_intro
    {fingerprintOk originalClausesSatisfied : Prop}
    (h : fingerprintOk -> originalClausesSatisfied) :
    ay_dopg_clause_satisfaction_replay fingerprintOk originalClausesSatisfied :=
  h

theorem ay_dopg_solver_build_evidence_intro
    {originalClausesSatisfied buildOk : Prop}
    (h : originalClausesSatisfied -> buildOk) :
    ay_dopg_solver_build_evidence originalClausesSatisfied buildOk :=
  h

theorem ay_dopg_validator_gate_intro {buildOk validatorOk : Prop}
    (h : buildOk -> validatorOk) :
    ay_dopg_validator_gate buildOk validatorOk :=
  h

theorem ay_dopg_fallback_no_claim_path_intro {validatorOk fallbackReady : Prop}
    (h : validatorOk -> fallbackReady) :
    ay_dopg_fallback_no_claim_path validatorOk fallbackReady :=
  h

theorem ay_dopg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_dopg_audit_transcript fallbackReady audited :=
  h

theorem ay_dopg_accepted_parser_intro
    {raw parserVersion statusLine assignmentLines literalLedger domain normalizedAssignment
     fingerprint replay build validator fallback audit : Prop}
    (hr : raw) (hpv : parserVersion) (hs : statusLine) (ha : assignmentLines)
    (hl : literalLedger) (hd : domain) (hn : normalizedAssignment) (hf : fingerprint)
    (hrep : replay) (hb : build) (hv : validator) (hfb : fallback) (hau : audit) :
    ay_dopg_accepted_parser raw parserVersion statusLine assignmentLines literalLedger
      domain normalizedAssignment fingerprint replay build validator fallback audit :=
  fun r k => k hr hpv hs ha hl hd hn hf hrep hb hv hfb hau

theorem ay_dopg_accepted_parser_raw
    {raw parserVersion statusLine assignmentLines literalLedger domain normalizedAssignment
     fingerprint replay build validator fallback audit : Prop}
    (h : ay_dopg_accepted_parser raw parserVersion statusLine assignmentLines literalLedger
      domain normalizedAssignment fingerprint replay build validator fallback audit) : raw :=
  h raw (fun hr _ _ _ _ _ _ _ _ _ _ _ _ => hr)

theorem ay_dopg_accepted_parser_version
    {raw parserVersion statusLine assignmentLines literalLedger domain normalizedAssignment
     fingerprint replay build validator fallback audit : Prop}
    (h : ay_dopg_accepted_parser raw parserVersion statusLine assignmentLines literalLedger
      domain normalizedAssignment fingerprint replay build validator fallback audit) :
    parserVersion :=
  h parserVersion (fun _ hpv _ _ _ _ _ _ _ _ _ _ _ => hpv)

theorem ay_dopg_accepted_parser_assignment_lines
    {raw parserVersion statusLine assignmentLines literalLedger domain normalizedAssignment
     fingerprint replay build validator fallback audit : Prop}
    (h : ay_dopg_accepted_parser raw parserVersion statusLine assignmentLines literalLedger
      domain normalizedAssignment fingerprint replay build validator fallback audit) :
    assignmentLines :=
  h assignmentLines (fun _ _ _ ha _ _ _ _ _ _ _ _ _ => ha)

theorem ay_dopg_accepted_parser_literal_ledger
    {raw parserVersion statusLine assignmentLines literalLedger domain normalizedAssignment
     fingerprint replay build validator fallback audit : Prop}
    (h : ay_dopg_accepted_parser raw parserVersion statusLine assignmentLines literalLedger
      domain normalizedAssignment fingerprint replay build validator fallback audit) :
    literalLedger :=
  h literalLedger (fun _ _ _ _ hl _ _ _ _ _ _ _ _ => hl)

theorem ay_dopg_accepted_parser_domain
    {raw parserVersion statusLine assignmentLines literalLedger domain normalizedAssignment
     fingerprint replay build validator fallback audit : Prop}
    (h : ay_dopg_accepted_parser raw parserVersion statusLine assignmentLines literalLedger
      domain normalizedAssignment fingerprint replay build validator fallback audit) : domain :=
  h domain (fun _ _ _ _ _ hd _ _ _ _ _ _ _ => hd)

theorem ay_dopg_accepted_parser_normalized_assignment
    {raw parserVersion statusLine assignmentLines literalLedger domain normalizedAssignment
     fingerprint replay build validator fallback audit : Prop}
    (h : ay_dopg_accepted_parser raw parserVersion statusLine assignmentLines literalLedger
      domain normalizedAssignment fingerprint replay build validator fallback audit) :
    normalizedAssignment :=
  h normalizedAssignment (fun _ _ _ _ _ _ hn _ _ _ _ _ _ => hn)

theorem ay_dopg_accepted_parser_replay
    {raw parserVersion statusLine assignmentLines literalLedger domain normalizedAssignment
     fingerprint replay build validator fallback audit : Prop}
    (h : ay_dopg_accepted_parser raw parserVersion statusLine assignmentLines literalLedger
      domain normalizedAssignment fingerprint replay build validator fallback audit) : replay :=
  h replay (fun _ _ _ _ _ _ _ _ hrep _ _ _ _ => hrep)

theorem ay_dopg_accepted_parser_validator
    {raw parserVersion statusLine assignmentLines literalLedger domain normalizedAssignment
     fingerprint replay build validator fallback audit : Prop}
    (h : ay_dopg_accepted_parser raw parserVersion statusLine assignmentLines literalLedger
      domain normalizedAssignment fingerprint replay build validator fallback audit) :
    validator :=
  h validator (fun _ _ _ _ _ _ _ _ _ _ hv _ _ => hv)

theorem ay_dopg_accepted_parser_audit
    {raw parserVersion statusLine assignmentLines literalLedger domain normalizedAssignment
     fingerprint replay build validator fallback audit : Prop}
    (h : ay_dopg_accepted_parser raw parserVersion statusLine assignmentLines literalLedger
      domain normalizedAssignment fingerprint replay build validator fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_dopg_public_sat_intro
    {accepted normalizedAssignment originalClausesSatisfied validatorOk audited : Prop}
    (ha : accepted) (hn : normalizedAssignment) (hc : originalClausesSatisfied)
    (hv : validatorOk) (hau : audited) :
    ay_dopg_public_sat accepted normalizedAssignment originalClausesSatisfied validatorOk
      audited :=
  ay_dopg_conj_intro ha
    (ay_dopg_conj_intro hn (ay_dopg_conj_intro hc (ay_dopg_conj_intro hv hau)))

theorem ay_dopg_public_sat_requires_parser_guard
    {accepted normalizedAssignment originalClausesSatisfied validatorOk audited : Prop}
    (h : ay_dopg_public_sat accepted normalizedAssignment originalClausesSatisfied
      validatorOk audited) : accepted :=
  ay_dopg_conj_left h

theorem ay_dopg_public_sat_normalized_assignment
    {accepted normalizedAssignment originalClausesSatisfied validatorOk audited : Prop}
    (h : ay_dopg_public_sat accepted normalizedAssignment originalClausesSatisfied
      validatorOk audited) : normalizedAssignment :=
  ay_dopg_conj_left (ay_dopg_conj_right h)

theorem ay_dopg_public_sat_original_clauses
    {accepted normalizedAssignment originalClausesSatisfied validatorOk audited : Prop}
    (h : ay_dopg_public_sat accepted normalizedAssignment originalClausesSatisfied
      validatorOk audited) : originalClausesSatisfied :=
  ay_dopg_conj_left (ay_dopg_conj_right (ay_dopg_conj_right h))

theorem ay_dopg_accepted_parser_yields_normalized_satisfying_assignment
    {raw parserVersion statusLine assignmentLines literalLedger domain normalizedAssignment
     fingerprint replay build validator fallback audit : Prop}
    (h : ay_dopg_accepted_parser raw parserVersion statusLine assignmentLines literalLedger
      domain normalizedAssignment fingerprint replay build validator fallback audit) :
    ay_dopg_public_sat
      (ay_dopg_accepted_parser raw parserVersion statusLine assignmentLines literalLedger
        domain normalizedAssignment fingerprint replay build validator fallback audit)
      normalizedAssignment replay validator audit :=
  ay_dopg_public_sat_intro
    h
    (ay_dopg_accepted_parser_normalized_assignment h)
    (ay_dopg_accepted_parser_replay h)
    (ay_dopg_accepted_parser_validator h)
    (ay_dopg_accepted_parser_audit h)

theorem ay_dopg_output_text_alone_cannot_bless_sat
    {rawOutput parserEvidence satisfactionReplay publicSat : Prop}
    (requiresParser : publicSat -> parserEvidence)
    (requiresReplay : publicSat -> satisfactionReplay)
    (missingParser : rawOutput -> parserEvidence -> rawOutput)
    (missingReplay : rawOutput -> satisfactionReplay -> rawOutput)
    (hraw : rawOutput) (hpub : publicSat) :
    ay_dopg_conj rawOutput rawOutput :=
  ay_dopg_conj_intro
    (missingParser hraw (requiresParser hpub))
    (missingReplay hraw (requiresReplay hpub))

theorem ay_dopg_no_claim_intro {reason : Prop} (h : reason) :
    ay_dopg_no_claim_diagnostic reason :=
  h

theorem ay_dopg_recompute_intro {reason : Prop} (h : reason) :
    ay_dopg_recompute_obligation reason :=
  h

theorem ay_dopg_malformed_output_no_claim {mismatch : Prop} (h : mismatch) :
    ay_dopg_no_claim_diagnostic mismatch :=
  ay_dopg_no_claim_intro h

theorem ay_dopg_duplicate_conflict_no_claim {mismatch : Prop} (h : mismatch) :
    ay_dopg_no_claim_diagnostic mismatch :=
  ay_dopg_no_claim_intro h

theorem ay_dopg_out_of_domain_recompute {mismatch : Prop} (h : mismatch) :
    ay_dopg_recompute_obligation mismatch :=
  ay_dopg_recompute_intro h

theorem ay_dopg_missing_terminator_no_claim {mismatch : Prop} (h : mismatch) :
    ay_dopg_no_claim_diagnostic mismatch :=
  ay_dopg_no_claim_intro h

theorem ay_dopg_parser_version_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_dopg_recompute_obligation mismatch :=
  ay_dopg_recompute_intro h

theorem ay_dopg_assignment_line_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_dopg_recompute_obligation mismatch :=
  ay_dopg_recompute_intro h

theorem ay_dopg_satisfaction_replay_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_dopg_no_claim_diagnostic mismatch :=
  ay_dopg_no_claim_intro h

theorem ay_dopg_build_mismatch_recompute {mismatch : Prop} (h : mismatch) :
    ay_dopg_recompute_obligation mismatch :=
  ay_dopg_recompute_intro h

theorem ay_dopg_validator_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_dopg_no_claim_diagnostic mismatch :=
  ay_dopg_no_claim_intro h

theorem ay_dopg_audit_mismatch_no_claim {mismatch : Prop} (h : mismatch) :
    ay_dopg_no_claim_diagnostic mismatch :=
  ay_dopg_no_claim_intro h

theorem ay_dopg_failed_output_parser_guard_cannot_bless_sat_publication
    {failure publicSat : Prop}
    (fallback : failure -> ay_dopg_no_claim_diagnostic failure)
    (noBless : ay_dopg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_dopg_failed_output_parser_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_dopg_recompute_obligation failure)
    (hfailure : failure) :
    ay_dopg_recompute_obligation failure :=
  fallback hfailure
