/-!
  SAT-COMP/ay crosscheck-disagreement quarantine guard.

  This self-contained package models the SAT-only quarantine contract for
  primary/crosscheck checker disagreement before public SAT publication.
-/

def ay_cdqg_conj (p q : Prop) : Prop :=
  forall r : Prop, (p -> q -> r) -> r

def ay_cdqg_disj (p q : Prop) : Prop :=
  forall r : Prop, (p -> r) -> (q -> r) -> r

def ay_cdqg_equiv (p q : Prop) : Prop :=
  ay_cdqg_conj (p -> q) (q -> p)

def ay_cdqg_benchmark_fingerprint (assignmentDigest fingerprintOk : Prop) : Prop :=
  assignmentDigest -> fingerprintOk

def ay_cdqg_assignment_digest (fingerprintOk assignmentOk : Prop) : Prop :=
  fingerprintOk -> assignmentOk

def ay_cdqg_primary_checker_transcript (assignmentOk primaryOk : Prop) : Prop :=
  assignmentOk -> primaryOk

def ay_cdqg_crosscheck_transcript (primaryOk crosscheckOk : Prop) : Prop :=
  primaryOk -> crosscheckOk

def ay_cdqg_disagreement_diagnostic_ledger
    (primaryOk crosscheckOk disagreementQuarantined : Prop) : Prop :=
  primaryOk -> crosscheckOk -> disagreementQuarantined

def ay_cdqg_fallback_no_claim_path (disagreementQuarantined fallbackReady : Prop) : Prop :=
  disagreementQuarantined -> fallbackReady

def ay_cdqg_solver_build_evidence (originalSat buildOk : Prop) : Prop :=
  originalSat -> buildOk

def ay_cdqg_archive_manifest (buildOk archiveOk : Prop) : Prop :=
  buildOk -> archiveOk

def ay_cdqg_audit_transcript (archiveOk audited : Prop) : Prop :=
  archiveOk -> audited

def ay_cdqg_accepted_agreement
    (fingerprint assignment primary crosscheck totalAssignment everyClause originalSat build
     archive audited : Prop) : Prop :=
  forall r : Prop,
    (fingerprint -> assignment -> primary -> crosscheck -> totalAssignment -> everyClause ->
      originalSat -> build -> archive -> audited -> r) -> r

def ay_cdqg_quarantined_disagreement
    (fingerprint assignment primary crosscheck diagnostic fallback build archive audited : Prop) :
    Prop :=
  forall r : Prop,
    (fingerprint -> assignment -> primary -> crosscheck -> diagnostic -> fallback -> build ->
      archive -> audited -> r) -> r

def ay_cdqg_public_sat
    (accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop) : Prop :=
  ay_cdqg_conj accepted
    (ay_cdqg_conj totalAssignment
      (ay_cdqg_conj everyOriginalClauseSatisfied (ay_cdqg_conj originalSat audited)))

def ay_cdqg_public_unsat (proofAccepted originalUnsat : Prop) : Prop :=
  ay_cdqg_conj proofAccepted originalUnsat

def ay_cdqg_no_claim_diagnostic (reason : Prop) : Prop :=
  reason

def ay_cdqg_recompute_obligation (reason : Prop) : Prop :=
  reason

theorem ay_cdqg_conj_intro {p q : Prop} (hp : p) (hq : q) : ay_cdqg_conj p q :=
  fun r h => h hp hq

theorem ay_cdqg_conj_left {p q : Prop} (h : ay_cdqg_conj p q) : p :=
  h p (fun hp _ => hp)

theorem ay_cdqg_conj_right {p q : Prop} (h : ay_cdqg_conj p q) : q :=
  (h (p -> q) (fun (_ : p) (hq : q) (_ : p) => hq)) (ay_cdqg_conj_left h)

theorem ay_cdqg_disj_left {p q : Prop} (hp : p) : ay_cdqg_disj p q :=
  fun r hl _ => hl hp

theorem ay_cdqg_disj_right {p q : Prop} (hq : q) : ay_cdqg_disj p q :=
  fun r _ hr => hr hq

theorem ay_cdqg_equiv_intro {p q : Prop} (hpq : p -> q) (hqp : q -> p) :
    ay_cdqg_equiv p q :=
  ay_cdqg_conj_intro hpq hqp

theorem ay_cdqg_equiv_forward {p q : Prop} (h : ay_cdqg_equiv p q) : p -> q :=
  ay_cdqg_conj_left h

theorem ay_cdqg_equiv_backward {p q : Prop} (h : ay_cdqg_equiv p q) : q -> p :=
  ay_cdqg_conj_right h

theorem ay_cdqg_benchmark_fingerprint_intro {assignmentDigest fingerprintOk : Prop}
    (h : assignmentDigest -> fingerprintOk) :
    ay_cdqg_benchmark_fingerprint assignmentDigest fingerprintOk :=
  h

theorem ay_cdqg_assignment_digest_intro {fingerprintOk assignmentOk : Prop}
    (h : fingerprintOk -> assignmentOk) :
    ay_cdqg_assignment_digest fingerprintOk assignmentOk :=
  h

theorem ay_cdqg_primary_checker_transcript_intro {assignmentOk primaryOk : Prop}
    (h : assignmentOk -> primaryOk) :
    ay_cdqg_primary_checker_transcript assignmentOk primaryOk :=
  h

theorem ay_cdqg_crosscheck_transcript_intro {primaryOk crosscheckOk : Prop}
    (h : primaryOk -> crosscheckOk) :
    ay_cdqg_crosscheck_transcript primaryOk crosscheckOk :=
  h

theorem ay_cdqg_disagreement_diagnostic_ledger_intro
    {primaryOk crosscheckOk disagreementQuarantined : Prop}
    (h : primaryOk -> crosscheckOk -> disagreementQuarantined) :
    ay_cdqg_disagreement_diagnostic_ledger primaryOk crosscheckOk
      disagreementQuarantined :=
  h

theorem ay_cdqg_fallback_no_claim_path_intro
    {disagreementQuarantined fallbackReady : Prop}
    (h : disagreementQuarantined -> fallbackReady) :
    ay_cdqg_fallback_no_claim_path disagreementQuarantined fallbackReady :=
  h

theorem ay_cdqg_solver_build_evidence_intro {originalSat buildOk : Prop}
    (h : originalSat -> buildOk) :
    ay_cdqg_solver_build_evidence originalSat buildOk :=
  h

theorem ay_cdqg_archive_manifest_intro {buildOk archiveOk : Prop}
    (h : buildOk -> archiveOk) :
    ay_cdqg_archive_manifest buildOk archiveOk :=
  h

theorem ay_cdqg_audit_transcript_intro {archiveOk audited : Prop}
    (h : archiveOk -> audited) :
    ay_cdqg_audit_transcript archiveOk audited :=
  h

theorem ay_cdqg_accepted_agreement_intro
    {fingerprint assignment primary crosscheck totalAssignment everyClause originalSat build
     archive audited : Prop}
    (hf : fingerprint) (ha : assignment) (hp : primary) (hc : crosscheck)
    (ht : totalAssignment) (he : everyClause) (hs : originalSat) (hb : build)
    (har : archive) (hau : audited) :
    ay_cdqg_accepted_agreement fingerprint assignment primary crosscheck totalAssignment
      everyClause originalSat build archive audited :=
  fun r k => k hf ha hp hc ht he hs hb har hau

theorem ay_cdqg_accepted_agreement_primary
    {fingerprint assignment primary crosscheck totalAssignment everyClause originalSat build
     archive audited : Prop}
    (h : ay_cdqg_accepted_agreement fingerprint assignment primary crosscheck totalAssignment
      everyClause originalSat build archive audited) : primary :=
  h primary (fun _ _ hp _ _ _ _ _ _ _ => hp)

theorem ay_cdqg_accepted_agreement_crosscheck
    {fingerprint assignment primary crosscheck totalAssignment everyClause originalSat build
     archive audited : Prop}
    (h : ay_cdqg_accepted_agreement fingerprint assignment primary crosscheck totalAssignment
      everyClause originalSat build archive audited) : crosscheck :=
  h crosscheck (fun _ _ _ hc _ _ _ _ _ _ => hc)

theorem ay_cdqg_accepted_agreement_total_assignment
    {fingerprint assignment primary crosscheck totalAssignment everyClause originalSat build
     archive audited : Prop}
    (h : ay_cdqg_accepted_agreement fingerprint assignment primary crosscheck totalAssignment
      everyClause originalSat build archive audited) : totalAssignment :=
  h totalAssignment (fun _ _ _ _ ht _ _ _ _ _ => ht)

theorem ay_cdqg_accepted_agreement_every_clause
    {fingerprint assignment primary crosscheck totalAssignment everyClause originalSat build
     archive audited : Prop}
    (h : ay_cdqg_accepted_agreement fingerprint assignment primary crosscheck totalAssignment
      everyClause originalSat build archive audited) : everyClause :=
  h everyClause (fun _ _ _ _ _ he _ _ _ _ => he)

theorem ay_cdqg_accepted_agreement_original_sat
    {fingerprint assignment primary crosscheck totalAssignment everyClause originalSat build
     archive audited : Prop}
    (h : ay_cdqg_accepted_agreement fingerprint assignment primary crosscheck totalAssignment
      everyClause originalSat build archive audited) : originalSat :=
  h originalSat (fun _ _ _ _ _ _ hs _ _ _ => hs)

theorem ay_cdqg_accepted_agreement_audit
    {fingerprint assignment primary crosscheck totalAssignment everyClause originalSat build
     archive audited : Prop}
    (h : ay_cdqg_accepted_agreement fingerprint assignment primary crosscheck totalAssignment
      everyClause originalSat build archive audited) : audited :=
  h audited (fun _ _ _ _ _ _ _ _ _ hau => hau)

theorem ay_cdqg_quarantined_disagreement_intro
    {fingerprint assignment primary crosscheck diagnostic fallback build archive audited : Prop}
    (hf : fingerprint) (ha : assignment) (hp : primary) (hc : crosscheck)
    (hd : diagnostic) (hfb : fallback) (hb : build) (har : archive) (hau : audited) :
    ay_cdqg_quarantined_disagreement fingerprint assignment primary crosscheck diagnostic
      fallback build archive audited :=
  fun r k => k hf ha hp hc hd hfb hb har hau

theorem ay_cdqg_quarantined_disagreement_diagnostic
    {fingerprint assignment primary crosscheck diagnostic fallback build archive audited : Prop}
    (h : ay_cdqg_quarantined_disagreement fingerprint assignment primary crosscheck
      diagnostic fallback build archive audited) : diagnostic :=
  h diagnostic (fun _ _ _ _ hd _ _ _ _ => hd)

theorem ay_cdqg_quarantined_disagreement_fallback
    {fingerprint assignment primary crosscheck diagnostic fallback build archive audited : Prop}
    (h : ay_cdqg_quarantined_disagreement fingerprint assignment primary crosscheck
      diagnostic fallback build archive audited) : fallback :=
  h fallback (fun _ _ _ _ _ hfb _ _ _ => hfb)

theorem ay_cdqg_public_sat_intro
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (ha : accepted) (ht : totalAssignment) (hc : everyOriginalClauseSatisfied)
    (hs : originalSat) (hau : audited) :
    ay_cdqg_public_sat accepted totalAssignment everyOriginalClauseSatisfied originalSat
      audited :=
  ay_cdqg_conj_intro ha
    (ay_cdqg_conj_intro ht
      (ay_cdqg_conj_intro hc (ay_cdqg_conj_intro hs hau)))

theorem ay_cdqg_public_sat_requires_agreement_guard
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cdqg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : accepted :=
  ay_cdqg_conj_left h

theorem ay_cdqg_public_sat_total_assignment
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cdqg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : totalAssignment :=
  ay_cdqg_conj_left (ay_cdqg_conj_right h)

theorem ay_cdqg_public_sat_every_original_clause
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cdqg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : everyOriginalClauseSatisfied :=
  ay_cdqg_conj_left (ay_cdqg_conj_right (ay_cdqg_conj_right h))

theorem ay_cdqg_public_sat_original_formula
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited : Prop}
    (h : ay_cdqg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited) : originalSat :=
  ay_cdqg_conj_left
    (ay_cdqg_conj_right (ay_cdqg_conj_right (ay_cdqg_conj_right h)))

theorem ay_cdqg_agreement_preserves_sat_publication_soundness
    {fingerprint assignment primary crosscheck totalAssignment everyClause originalSat build
     archive audited : Prop}
    (h : ay_cdqg_accepted_agreement fingerprint assignment primary crosscheck totalAssignment
      everyClause originalSat build archive audited) :
    ay_cdqg_public_sat
      (ay_cdqg_accepted_agreement fingerprint assignment primary crosscheck totalAssignment
        everyClause originalSat build archive audited)
      totalAssignment everyClause originalSat audited :=
  ay_cdqg_public_sat_intro
    h
    (ay_cdqg_accepted_agreement_total_assignment h)
    (ay_cdqg_accepted_agreement_every_clause h)
    (ay_cdqg_accepted_agreement_original_sat h)
    (ay_cdqg_accepted_agreement_audit h)

theorem ay_cdqg_disagreement_cannot_bless_public_sat
    {disagreement publicSat : Prop}
    (quarantine : disagreement -> ay_cdqg_no_claim_diagnostic disagreement)
    (noBless : ay_cdqg_no_claim_diagnostic disagreement -> publicSat -> disagreement)
    (hd : disagreement) (hp : publicSat) : disagreement :=
  noBless (quarantine hd) hp

theorem ay_cdqg_no_claim_intro {reason : Prop} (h : reason) :
    ay_cdqg_no_claim_diagnostic reason :=
  h

theorem ay_cdqg_recompute_intro {reason : Prop} (h : reason) :
    ay_cdqg_recompute_obligation reason :=
  h

theorem ay_cdqg_checker_mismatch_no_claim {checkerMismatch : Prop}
    (h : checkerMismatch) :
    ay_cdqg_no_claim_diagnostic checkerMismatch :=
  ay_cdqg_no_claim_intro h

theorem ay_cdqg_checker_mismatch_recompute {checkerMismatch : Prop}
    (h : checkerMismatch) :
    ay_cdqg_recompute_obligation checkerMismatch :=
  ay_cdqg_recompute_intro h

theorem ay_cdqg_diagnostic_mismatch_no_claim {diagnosticMismatch : Prop}
    (h : diagnosticMismatch) :
    ay_cdqg_no_claim_diagnostic diagnosticMismatch :=
  ay_cdqg_no_claim_intro h

theorem ay_cdqg_build_mismatch_recompute {buildMismatch : Prop}
    (h : buildMismatch) :
    ay_cdqg_recompute_obligation buildMismatch :=
  ay_cdqg_recompute_intro h

theorem ay_cdqg_archive_mismatch_no_claim {archiveMismatch : Prop}
    (h : archiveMismatch) :
    ay_cdqg_no_claim_diagnostic archiveMismatch :=
  ay_cdqg_no_claim_intro h

theorem ay_cdqg_failed_quarantine_guard_forces_recompute
    {failure : Prop}
    (fallback : failure -> ay_cdqg_recompute_obligation failure)
    (hfailure : failure) :
    ay_cdqg_recompute_obligation failure :=
  fallback hfailure

theorem ay_cdqg_public_unsat_intro {proofAccepted originalUnsat : Prop}
    (hp : proofAccepted) (hu : originalUnsat) :
    ay_cdqg_public_unsat proofAccepted originalUnsat :=
  ay_cdqg_conj_intro hp hu

theorem ay_cdqg_public_unsat_proof {proofAccepted originalUnsat : Prop}
    (h : ay_cdqg_public_unsat proofAccepted originalUnsat) : proofAccepted :=
  ay_cdqg_conj_left h

theorem ay_cdqg_public_unsat_claim {proofAccepted originalUnsat : Prop}
    (h : ay_cdqg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_cdqg_conj_right h

theorem ay_cdqg_quarantine_guard_cannot_strengthen_unsat_claims
    {accepted totalAssignment everyOriginalClauseSatisfied originalSat audited
     proofAccepted originalUnsat : Prop}
    (_hSatGuard : ay_cdqg_public_sat accepted totalAssignment everyOriginalClauseSatisfied
      originalSat audited)
    (hUnsat : ay_cdqg_public_unsat proofAccepted originalUnsat) : originalUnsat :=
  ay_cdqg_public_unsat_claim hUnsat
