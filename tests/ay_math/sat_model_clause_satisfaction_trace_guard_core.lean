/-!
  SAT-COMP/ay clause-satisfaction trace guard.

  This self-contained package models the SAT-only obligations for trusting a
  clause-satisfaction trace digest before publishing a public SAT witness.
-/

def ay_cstg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_cstg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_cstg_equiv (p q : Prop) : Prop :=
  ay_cstg_conj (p -> q) (q -> p)

def ay_cstg_benchmark_fingerprint (assignmentDigest fingerprintOk : Prop) : Prop :=
  assignmentDigest -> fingerprintOk

def ay_cstg_assignment_digest (fingerprintOk assignmentOk : Prop) : Prop :=
  fingerprintOk -> assignmentOk

def ay_cstg_clause_satisfaction_trace_digest (assignmentOk traceOk : Prop) : Prop :=
  assignmentOk -> traceOk

def ay_cstg_per_clause_satisfied_literal_witness_ledger
    (traceOk witnessLedgerOk : Prop) : Prop :=
  traceOk -> witnessLedgerOk

def ay_cstg_variable_domain_manifest (witnessLedgerOk domainOk : Prop) : Prop :=
  witnessLedgerOk -> domainOk

def ay_cstg_total_assignment_reconstruction (domainOk totalAssignment : Prop) : Prop :=
  domainOk -> totalAssignment

def ay_cstg_model_checker_transcript
    (everyOriginalClauseSatisfied originalSat : Prop) : Prop :=
  everyOriginalClauseSatisfied -> originalSat

def ay_cstg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_cstg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_cstg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_cstg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_cstg_accepted_trace
    (fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop) : Prop :=
  forall r : Prop,
    (fingerprint -> assignment -> trace -> witness -> domain -> reconstruction ->
      everyClause -> checker -> build -> archive -> fallback -> audit -> r) -> r

def ay_cstg_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_cstg_conj accepted
    (ay_cstg_conj totalAssignment
      (ay_cstg_conj everyOriginalClauseSatisfied (ay_cstg_conj originalSat audited)))

def ay_cstg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_cstg_conj proofAccepted originalUnsat

def ay_cstg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_cstg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_cstg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_cstg_conj p q :=
  fun r h => h hp hq

theorem ay_cstg_conj_left {p q : Prop} (h : ay_cstg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_cstg_conj_right {p q : Prop} (h : ay_cstg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_cstg_conj_left h)

theorem ay_cstg_disj_left {p q : Prop} (hp : p) : ay_cstg_disj p q :=
  fun r hl _ => hl hp

theorem ay_cstg_disj_right {p q : Prop} (hq : q) : ay_cstg_disj p q :=
  fun r _ hr => hr hq

theorem ay_cstg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_cstg_equiv p q :=
  ay_cstg_conj_intro hpq hqp

theorem ay_cstg_equiv_forward {p q : Prop} (h : ay_cstg_equiv p q) : p -> q :=
  ay_cstg_conj_left h

theorem ay_cstg_equiv_backward {p q : Prop} (h : ay_cstg_equiv p q) : q -> p :=
  ay_cstg_conj_right h

theorem ay_cstg_benchmark_fingerprint_intro {assignmentDigest fingerprintOk : Prop}
    (h : assignmentDigest -> fingerprintOk) :
    ay_cstg_benchmark_fingerprint assignmentDigest fingerprintOk :=
  h

theorem ay_cstg_assignment_digest_intro {fingerprintOk assignmentOk : Prop}
    (h : fingerprintOk -> assignmentOk) :
    ay_cstg_assignment_digest fingerprintOk assignmentOk :=
  h

theorem ay_cstg_clause_satisfaction_trace_digest_intro {assignmentOk traceOk : Prop}
    (h : assignmentOk -> traceOk) :
    ay_cstg_clause_satisfaction_trace_digest assignmentOk traceOk :=
  h

theorem ay_cstg_per_clause_satisfied_literal_witness_ledger_intro
    {traceOk witnessLedgerOk : Prop}
    (h : traceOk -> witnessLedgerOk) :
    ay_cstg_per_clause_satisfied_literal_witness_ledger traceOk witnessLedgerOk :=
  h

theorem ay_cstg_variable_domain_manifest_intro {witnessLedgerOk domainOk : Prop}
    (h : witnessLedgerOk -> domainOk) :
    ay_cstg_variable_domain_manifest witnessLedgerOk domainOk :=
  h

theorem ay_cstg_total_assignment_reconstruction_intro
    {domainOk totalAssignment : Prop}
    (h : domainOk -> totalAssignment) :
    ay_cstg_total_assignment_reconstruction domainOk totalAssignment :=
  h

theorem ay_cstg_model_checker_transcript_intro
    {everyOriginalClauseSatisfied originalSat : Prop}
    (h : everyOriginalClauseSatisfied -> originalSat) :
    ay_cstg_model_checker_transcript everyOriginalClauseSatisfied originalSat :=
  h

theorem ay_cstg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_cstg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_cstg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_cstg_archive_manifest buildOk archiveOk :=
  h

theorem ay_cstg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_cstg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_cstg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_cstg_audit_transcript fallbackReady audited :=
  h

theorem ay_cstg_accepted_trace_intro
    {fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop}
    (hf : fingerprint) (ha : assignment) (ht : trace) (hw : witness) (hd : domain)
    (hrc : reconstruction) (he : everyClause) (hchk : checker) (hb : build)
    (har : archive) (hfb : fallback) (hau : audit) :
    ay_cstg_accepted_trace fingerprint assignment trace witness domain reconstruction
      everyClause checker build archive fallback audit :=
  fun r k => k hf ha ht hw hd hrc he hchk hb har hfb hau

theorem ay_cstg_accepted_trace_fingerprint
    {fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop}
    (h : ay_cstg_accepted_trace fingerprint assignment trace witness domain reconstruction
      everyClause checker build archive fallback audit) : fingerprint :=
  h fingerprint (fun hf _ _ _ _ _ _ _ _ _ _ _ => hf)

theorem ay_cstg_accepted_trace_assignment
    {fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop}
    (h : ay_cstg_accepted_trace fingerprint assignment trace witness domain reconstruction
      everyClause checker build archive fallback audit) : assignment :=
  h assignment (fun _ ha _ _ _ _ _ _ _ _ _ _ => ha)

theorem ay_cstg_accepted_trace_trace
    {fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop}
    (h : ay_cstg_accepted_trace fingerprint assignment trace witness domain reconstruction
      everyClause checker build archive fallback audit) : trace :=
  h trace (fun _ _ ht _ _ _ _ _ _ _ _ _ => ht)

theorem ay_cstg_accepted_trace_witness
    {fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop}
    (h : ay_cstg_accepted_trace fingerprint assignment trace witness domain reconstruction
      everyClause checker build archive fallback audit) : witness :=
  h witness (fun _ _ _ hw _ _ _ _ _ _ _ _ => hw)

theorem ay_cstg_accepted_trace_domain
    {fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop}
    (h : ay_cstg_accepted_trace fingerprint assignment trace witness domain reconstruction
      everyClause checker build archive fallback audit) : domain :=
  h domain (fun _ _ _ _ hd _ _ _ _ _ _ _ => hd)

theorem ay_cstg_accepted_trace_reconstruction
    {fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop}
    (h : ay_cstg_accepted_trace fingerprint assignment trace witness domain reconstruction
      everyClause checker build archive fallback audit) : reconstruction :=
  h reconstruction (fun _ _ _ _ _ hrc _ _ _ _ _ _ => hrc)

theorem ay_cstg_accepted_trace_every_clause
    {fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop}
    (h : ay_cstg_accepted_trace fingerprint assignment trace witness domain reconstruction
      everyClause checker build archive fallback audit) : everyClause :=
  h everyClause (fun _ _ _ _ _ _ he _ _ _ _ _ => he)

theorem ay_cstg_accepted_trace_checker
    {fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop}
    (h : ay_cstg_accepted_trace fingerprint assignment trace witness domain reconstruction
      everyClause checker build archive fallback audit) : checker :=
  h checker (fun _ _ _ _ _ _ _ hchk _ _ _ _ => hchk)

theorem ay_cstg_accepted_trace_build
    {fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop}
    (h : ay_cstg_accepted_trace fingerprint assignment trace witness domain reconstruction
      everyClause checker build archive fallback audit) : build :=
  h build (fun _ _ _ _ _ _ _ _ hb _ _ _ => hb)

theorem ay_cstg_accepted_trace_archive
    {fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop}
    (h : ay_cstg_accepted_trace fingerprint assignment trace witness domain reconstruction
      everyClause checker build archive fallback audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ _ har _ _ => har)

theorem ay_cstg_accepted_trace_fallback
    {fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop}
    (h : ay_cstg_accepted_trace fingerprint assignment trace witness domain reconstruction
      everyClause checker build archive fallback audit) : fallback :=
  h fallback (fun _ _ _ _ _ _ _ _ _ _ hfb _ => hfb)

theorem ay_cstg_accepted_trace_audit
    {fingerprint assignment trace witness domain reconstruction everyClause checker build archive
     fallback audit : Prop}
    (h : ay_cstg_accepted_trace fingerprint assignment trace witness domain reconstruction
      everyClause checker build archive fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_cstg_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hc : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_cstg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_cstg_conj_intro ha
    (ay_cstg_conj_intro ht
      (ay_cstg_conj_intro hc (ay_cstg_conj_intro hs hau)))

theorem ay_cstg_public_sat_requires_trace_guard
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cstg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : accepted :=
  ay_cstg_conj_left h

theorem ay_cstg_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cstg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : totalAssignment :=
  ay_cstg_conj_left (ay_cstg_conj_right h)

theorem ay_cstg_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cstg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : everyOriginalClauseSatisfied :=
  ay_cstg_conj_left (ay_cstg_conj_right (ay_cstg_conj_right h))

theorem ay_cstg_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cstg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : originalSat :=
  ay_cstg_conj_left
    (ay_cstg_conj_right (ay_cstg_conj_right (ay_cstg_conj_right h)))

theorem ay_cstg_public_sat_audit
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cstg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : audited :=
  ay_cstg_conj_right
    (ay_cstg_conj_right (ay_cstg_conj_right (ay_cstg_conj_right h)))

theorem ay_cstg_trace_evidence_satisfies_every_original_clause
    {fingerprint assignment trace witness domain totalAssignment everyOriginalClauseSatisfied
     originalSat build archive fallback audited : Prop}
    (h : ay_cstg_accepted_trace fingerprint assignment trace witness domain totalAssignment
      everyOriginalClauseSatisfied originalSat build archive fallback audited) :
    ay_cstg_public_sat
      (ay_cstg_accepted_trace fingerprint assignment trace witness domain totalAssignment
        everyOriginalClauseSatisfied originalSat build archive fallback audited)
      totalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_cstg_public_sat_intro
    h
    (ay_cstg_accepted_trace_reconstruction h)
    (ay_cstg_accepted_trace_every_clause h)
    (ay_cstg_accepted_trace_checker h)
    (ay_cstg_accepted_trace_audit h)

theorem ay_cstg_witness_ledger_implies_clause_trace
    {trace witness everyClause : Prop}
    (h : ay_cstg_equiv trace witness)
    (hw : witness -> everyClause) (ht : trace) : everyClause :=
  hw (ay_cstg_equiv_forward h ht)

theorem ay_cstg_no_claim_intro {reason : Prop} (h : reason) :
    ay_cstg_no_claim_diagnostic reason :=
  h

theorem ay_cstg_recompute_intro {reason : Prop} (h : reason) :
    ay_cstg_recompute_obligation reason :=
  h

theorem ay_cstg_trace_mismatch_no_claim {traceMismatch : Prop}
    (h : traceMismatch) :
    ay_cstg_no_claim_diagnostic traceMismatch :=
  ay_cstg_no_claim_intro h

theorem ay_cstg_trace_mismatch_recompute {traceMismatch : Prop}
    (h : traceMismatch) :
    ay_cstg_recompute_obligation traceMismatch :=
  ay_cstg_recompute_intro h

theorem ay_cstg_witness_mismatch_no_claim {witnessMismatch : Prop}
    (h : witnessMismatch) :
    ay_cstg_no_claim_diagnostic witnessMismatch :=
  ay_cstg_no_claim_intro h

theorem ay_cstg_domain_mismatch_no_claim {domainMismatch : Prop}
    (h : domainMismatch) :
    ay_cstg_no_claim_diagnostic domainMismatch :=
  ay_cstg_no_claim_intro h

theorem ay_cstg_reconstruction_mismatch_recompute {reconstructionMismatch : Prop}
    (h : reconstructionMismatch) :
    ay_cstg_recompute_obligation reconstructionMismatch :=
  ay_cstg_recompute_intro h

theorem ay_cstg_checker_mismatch_no_claim {checkerMismatch : Prop}
    (h : checkerMismatch) :
    ay_cstg_no_claim_diagnostic checkerMismatch :=
  ay_cstg_no_claim_intro h

theorem ay_cstg_build_mismatch_recompute {buildMismatch : Prop}
    (h : buildMismatch) :
    ay_cstg_recompute_obligation buildMismatch :=
  ay_cstg_recompute_intro h

theorem ay_cstg_archive_mismatch_no_claim {archiveMismatch : Prop}
    (h : archiveMismatch) :
    ay_cstg_no_claim_diagnostic archiveMismatch :=
  ay_cstg_no_claim_intro h

theorem ay_cstg_failed_trace_guard_cannot_create_public_sat
    {failure publicSat : Prop}
    (fallback : failure -> ay_cstg_no_claim_diagnostic failure)
    (noBless : ay_cstg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_cstg_failed_trace_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_cstg_recompute_obligation failure)
    (hfailure : failure) :
    ay_cstg_recompute_obligation failure :=
  fallback hfailure

theorem ay_cstg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_cstg_public_unsat proofAccepted originalUnsat :=
  ay_cstg_conj_intro hp hu

theorem ay_cstg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_cstg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_cstg_conj_left h

theorem ay_cstg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_cstg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_cstg_conj_right h

theorem ay_cstg_trace_guard_cannot_strengthen_unsat_claims
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited
     proofAccepted originalUnsat : Prop}
    (_hSatGuard : ay_cstg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited)
    (hUnsat : ay_cstg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_cstg_public_unsat_claim hUnsat
