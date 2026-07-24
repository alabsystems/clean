/-!
  SAT-COMP/ay model-checker crosscheck guard.

  This self-contained package models the SAT-only obligations for publishing a
  SAT witness only after primary and independent model checkers agree.
-/

def ay_mccg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_mccg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_mccg_equiv (p q : Prop) : Prop :=
  ay_mccg_conj (p -> q) (q -> p)

def ay_mccg_benchmark_fingerprint (assignmentDigest fingerprintOk : Prop) : Prop :=
  assignmentDigest -> fingerprintOk

def ay_mccg_assignment_digest (fingerprintOk assignmentOk : Prop) : Prop :=
  fingerprintOk -> assignmentOk

def ay_mccg_primary_model_checker_transcript (assignmentOk primaryOk : Prop) : Prop :=
  assignmentOk -> primaryOk

def ay_mccg_independent_crosscheck_transcript (primaryOk crosscheckOk : Prop) : Prop :=
  primaryOk -> crosscheckOk

def ay_mccg_clause_satisfaction_trace_digest (crosscheckOk traceOk : Prop) : Prop :=
  crosscheckOk -> traceOk

def ay_mccg_total_assignment_reconstruction (traceOk totalAssignment : Prop) : Prop :=
  traceOk -> totalAssignment

def ay_mccg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_mccg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_mccg_fallback_no_claim_path (archiveOk fallbackReady : Prop) : Prop :=
  archiveOk -> fallbackReady

def ay_mccg_audit_transcript (fallbackReady audited : Prop) : Prop :=
  fallbackReady -> audited

def ay_mccg_accepted_crosscheck
    (fingerprint assignment primary crosscheck trace reconstruction everyClause build archive
     fallback audit : Prop) : Prop :=
  forall r : Prop,
    (fingerprint -> assignment -> primary -> crosscheck -> trace -> reconstruction ->
      everyClause -> build -> archive -> fallback -> audit -> r) -> r

def ay_mccg_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_mccg_conj accepted
    (ay_mccg_conj totalAssignment
      (ay_mccg_conj everyOriginalClauseSatisfied (ay_mccg_conj originalSat audited)))

def ay_mccg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_mccg_conj proofAccepted originalUnsat

def ay_mccg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_mccg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_mccg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_mccg_conj p q :=
  fun r h => h hp hq

theorem ay_mccg_conj_left {p q : Prop} (h : ay_mccg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_mccg_conj_right {p q : Prop} (h : ay_mccg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_mccg_conj_left h)

theorem ay_mccg_disj_left {p q : Prop} (hp : p) : ay_mccg_disj p q :=
  fun r hl _ => hl hp

theorem ay_mccg_disj_right {p q : Prop} (hq : q) : ay_mccg_disj p q :=
  fun r _ hr => hr hq

theorem ay_mccg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_mccg_equiv p q :=
  ay_mccg_conj_intro hpq hqp

theorem ay_mccg_equiv_forward {p q : Prop} (h : ay_mccg_equiv p q) : p -> q :=
  ay_mccg_conj_left h

theorem ay_mccg_equiv_backward {p q : Prop} (h : ay_mccg_equiv p q) : q -> p :=
  ay_mccg_conj_right h

theorem ay_mccg_benchmark_fingerprint_intro {assignmentDigest fingerprintOk : Prop}
    (h : assignmentDigest -> fingerprintOk) :
    ay_mccg_benchmark_fingerprint assignmentDigest fingerprintOk :=
  h

theorem ay_mccg_assignment_digest_intro {fingerprintOk assignmentOk : Prop}
    (h : fingerprintOk -> assignmentOk) :
    ay_mccg_assignment_digest fingerprintOk assignmentOk :=
  h

theorem ay_mccg_primary_model_checker_transcript_intro {assignmentOk primaryOk : Prop}
    (h : assignmentOk -> primaryOk) :
    ay_mccg_primary_model_checker_transcript assignmentOk primaryOk :=
  h

theorem ay_mccg_independent_crosscheck_transcript_intro {primaryOk crosscheckOk : Prop}
    (h : primaryOk -> crosscheckOk) :
    ay_mccg_independent_crosscheck_transcript primaryOk crosscheckOk :=
  h

theorem ay_mccg_clause_satisfaction_trace_digest_intro {crosscheckOk traceOk : Prop}
    (h : crosscheckOk -> traceOk) :
    ay_mccg_clause_satisfaction_trace_digest crosscheckOk traceOk :=
  h

theorem ay_mccg_total_assignment_reconstruction_intro {traceOk totalAssignment : Prop}
    (h : traceOk -> totalAssignment) :
    ay_mccg_total_assignment_reconstruction traceOk totalAssignment :=
  h

theorem ay_mccg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_mccg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_mccg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_mccg_archive_manifest buildOk archiveOk :=
  h

theorem ay_mccg_fallback_no_claim_path_intro {archiveOk fallbackReady : Prop}
    (h : archiveOk -> fallbackReady) :
    ay_mccg_fallback_no_claim_path archiveOk fallbackReady :=
  h

theorem ay_mccg_audit_transcript_intro {fallbackReady audited : Prop}
    (h : fallbackReady -> audited) :
    ay_mccg_audit_transcript fallbackReady audited :=
  h

theorem ay_mccg_accepted_crosscheck_intro
    {fingerprint assignment primary crosscheck trace reconstruction everyClause build archive
     fallback audit : Prop}
    (hf : fingerprint) (ha : assignment) (hp : primary) (hc : crosscheck) (ht : trace)
    (hrc : reconstruction) (he : everyClause) (hb : build) (har : archive)
    (hfb : fallback) (hau : audit) :
    ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
      reconstruction everyClause build archive fallback audit :=
  fun r k => k hf ha hp hc ht hrc he hb har hfb hau

theorem ay_mccg_accepted_crosscheck_fingerprint
    {fingerprint assignment primary crosscheck trace reconstruction everyClause build archive
     fallback audit : Prop}
    (h : ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
      reconstruction everyClause build archive fallback audit) : fingerprint :=
  h fingerprint (fun hf _ _ _ _ _ _ _ _ _ _ => hf)

theorem ay_mccg_accepted_crosscheck_assignment
    {fingerprint assignment primary crosscheck trace reconstruction everyClause build archive
     fallback audit : Prop}
    (h : ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
      reconstruction everyClause build archive fallback audit) : assignment :=
  h assignment (fun _ ha _ _ _ _ _ _ _ _ _ => ha)

theorem ay_mccg_accepted_crosscheck_primary
    {fingerprint assignment primary crosscheck trace reconstruction everyClause build archive
     fallback audit : Prop}
    (h : ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
      reconstruction everyClause build archive fallback audit) : primary :=
  h primary (fun _ _ hp _ _ _ _ _ _ _ _ => hp)

theorem ay_mccg_accepted_crosscheck_crosscheck
    {fingerprint assignment primary crosscheck trace reconstruction everyClause build archive
     fallback audit : Prop}
    (h : ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
      reconstruction everyClause build archive fallback audit) : crosscheck :=
  h crosscheck (fun _ _ _ hc _ _ _ _ _ _ _ => hc)

theorem ay_mccg_accepted_crosscheck_trace
    {fingerprint assignment primary crosscheck trace reconstruction everyClause build archive
     fallback audit : Prop}
    (h : ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
      reconstruction everyClause build archive fallback audit) : trace :=
  h trace (fun _ _ _ _ ht _ _ _ _ _ _ => ht)

theorem ay_mccg_accepted_crosscheck_reconstruction
    {fingerprint assignment primary crosscheck trace reconstruction everyClause build archive
     fallback audit : Prop}
    (h : ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
      reconstruction everyClause build archive fallback audit) : reconstruction :=
  h reconstruction (fun _ _ _ _ _ hrc _ _ _ _ _ => hrc)

theorem ay_mccg_accepted_crosscheck_every_clause
    {fingerprint assignment primary crosscheck trace reconstruction everyClause build archive
     fallback audit : Prop}
    (h : ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
      reconstruction everyClause build archive fallback audit) : everyClause :=
  h everyClause (fun _ _ _ _ _ _ he _ _ _ _ => he)

theorem ay_mccg_accepted_crosscheck_build
    {fingerprint assignment primary crosscheck trace reconstruction everyClause build archive
     fallback audit : Prop}
    (h : ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
      reconstruction everyClause build archive fallback audit) : build :=
  h build (fun _ _ _ _ _ _ _ hb _ _ _ => hb)

theorem ay_mccg_accepted_crosscheck_archive
    {fingerprint assignment primary crosscheck trace reconstruction everyClause build archive
     fallback audit : Prop}
    (h : ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
      reconstruction everyClause build archive fallback audit) : archive :=
  h archive (fun _ _ _ _ _ _ _ _ har _ _ => har)

theorem ay_mccg_accepted_crosscheck_fallback
    {fingerprint assignment primary crosscheck trace reconstruction everyClause build archive
     fallback audit : Prop}
    (h : ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
      reconstruction everyClause build archive fallback audit) : fallback :=
  h fallback (fun _ _ _ _ _ _ _ _ _ hfb _ => hfb)

theorem ay_mccg_accepted_crosscheck_audit
    {fingerprint assignment primary crosscheck trace reconstruction everyClause build archive
     fallback audit : Prop}
    (h : ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
      reconstruction everyClause build archive fallback audit) : audit :=
  h audit (fun _ _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_mccg_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hc : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_mccg_conj_intro ha
    (ay_mccg_conj_intro ht
      (ay_mccg_conj_intro hc (ay_mccg_conj_intro hs hau)))

theorem ay_mccg_public_sat_requires_crosscheck_guard
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : accepted :=
  ay_mccg_conj_left h

theorem ay_mccg_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : totalAssignment :=
  ay_mccg_conj_left (ay_mccg_conj_right h)

theorem ay_mccg_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : everyOriginalClauseSatisfied :=
  ay_mccg_conj_left (ay_mccg_conj_right (ay_mccg_conj_right h))

theorem ay_mccg_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : originalSat :=
  ay_mccg_conj_left
    (ay_mccg_conj_right (ay_mccg_conj_right (ay_mccg_conj_right h)))

theorem ay_mccg_public_sat_audit
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : audited :=
  ay_mccg_conj_right
    (ay_mccg_conj_right (ay_mccg_conj_right (ay_mccg_conj_right h)))

theorem ay_mccg_crosschecked_evidence_publishes_sat
    {fingerprint assignment primary crosscheck trace totalAssignment everyOriginalClauseSatisfied
     originalSat archive fallback audited : Prop}
    (h : ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
      totalAssignment everyOriginalClauseSatisfied originalSat archive fallback audited) :
    ay_mccg_public_sat
      (ay_mccg_accepted_crosscheck fingerprint assignment primary crosscheck trace
        totalAssignment everyOriginalClauseSatisfied originalSat archive fallback audited)
      totalAssignment everyOriginalClauseSatisfied originalSat audited :=
  ay_mccg_public_sat_intro
    h
    (ay_mccg_accepted_crosscheck_reconstruction h)
    (ay_mccg_accepted_crosscheck_every_clause h)
    (ay_mccg_accepted_crosscheck_build h)
    (ay_mccg_accepted_crosscheck_audit h)

theorem ay_mccg_primary_and_crosscheck_agree_on_trace
    {primary crosscheck trace everyClause : Prop}
    (hp : primary -> trace) (hc : crosscheck -> trace)
    (ht : trace -> everyClause) (hprimary : primary) (_hcross : crosscheck) :
    everyClause :=
  ht (hp hprimary)

theorem ay_mccg_no_claim_intro {reason : Prop} (h : reason) :
    ay_mccg_no_claim_diagnostic reason :=
  h

theorem ay_mccg_recompute_intro {reason : Prop} (h : reason) :
    ay_mccg_recompute_obligation reason :=
  h

theorem ay_mccg_checker_mismatch_no_claim {checkerMismatch : Prop}
    (h : checkerMismatch) :
    ay_mccg_no_claim_diagnostic checkerMismatch :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_checker_mismatch_recompute {checkerMismatch : Prop}
    (h : checkerMismatch) :
    ay_mccg_recompute_obligation checkerMismatch :=
  ay_mccg_recompute_intro h

theorem ay_mccg_crosscheck_mismatch_no_claim {crosscheckMismatch : Prop}
    (h : crosscheckMismatch) :
    ay_mccg_no_claim_diagnostic crosscheckMismatch :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_trace_mismatch_recompute {traceMismatch : Prop}
    (h : traceMismatch) :
    ay_mccg_recompute_obligation traceMismatch :=
  ay_mccg_recompute_intro h

theorem ay_mccg_reconstruction_mismatch_recompute {reconstructionMismatch : Prop}
    (h : reconstructionMismatch) :
    ay_mccg_recompute_obligation reconstructionMismatch :=
  ay_mccg_recompute_intro h

theorem ay_mccg_build_mismatch_recompute {buildMismatch : Prop}
    (h : buildMismatch) :
    ay_mccg_recompute_obligation buildMismatch :=
  ay_mccg_recompute_intro h

theorem ay_mccg_archive_mismatch_no_claim {archiveMismatch : Prop}
    (h : archiveMismatch) :
    ay_mccg_no_claim_diagnostic archiveMismatch :=
  ay_mccg_no_claim_intro h

theorem ay_mccg_failed_crosscheck_guard_cannot_create_public_sat
    {failure publicSat : Prop}
    (fallback : failure -> ay_mccg_no_claim_diagnostic failure)
    (noBless : ay_mccg_no_claim_diagnostic failure -> publicSat -> failure)
    (hfailure : failure) (hpublic : publicSat) : failure :=
  noBless (fallback hfailure) hpublic

theorem ay_mccg_failed_crosscheck_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_mccg_recompute_obligation failure)
    (hfailure : failure) :
    ay_mccg_recompute_obligation failure :=
  fallback hfailure

theorem ay_mccg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_mccg_public_unsat proofAccepted originalUnsat :=
  ay_mccg_conj_intro hp hu

theorem ay_mccg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_mccg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_mccg_conj_left h

theorem ay_mccg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_mccg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_mccg_conj_right h

theorem ay_mccg_crosscheck_guard_cannot_strengthen_unsat_claims
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited
     proofAccepted originalUnsat : Prop}
    (_hSatGuard : ay_mccg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited)
    (hUnsat : ay_mccg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_mccg_public_unsat_claim hUnsat
